defmodule Lynx.Rustler.RwLockTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_RWLOCK_DIR")
  @moduletag timeout: 1_200_000
  unless @tools, do: @moduletag(skip: "set LYNX_RWLOCK_DIR for read/write lock proofs")

  @tag :tmp_dir
  test "shared readers compose with a cross-crate writer and a compiled NIF", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    File.cp_r!(
      Path.expand("../rust_workspace/unrelated", @fixture),
      Path.join(workspace, "unrelated")
    )

    manifest = Path.join(workspace, "Cargo.toml")

    File.write!(
      manifest,
      String.replace(
        File.read!(manifest),
        ~s(["base", "app", "nif"]),
        ~s(["base", "app", "nif", "unrelated"])
      )
    )

    lock = Path.join(workspace, "Cargo.lock")

    File.write!(
      lock,
      File.read!(lock) <> ~s(\n[[package]]\nname = "experiment-unrelated"\nversion = "0.1.0"\n)
    )

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "LynxOwnershipFixture", "LynxRwLockFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Rw"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    property = Path.join(project, "Rw/Properties.lean")
    proof = File.read!(Path.join(@fixture, "RwLockProperties.lean"))
    File.write!(property, proof)

    File.cp!(
      Path.join(@fixture, "RwLockModelProperties.lean"),
      Path.join(project, "Rw/ModelProperties.lean")
    )

    common = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["rwlock"]],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Rw.Extraction"
    ]

    required =
      ~w(Rw.Properties.toggle_base Rw.Properties.toggle_app Rw.Properties.shared_then_exclusive)

    options =
      common ++
        [
          roots: ["ownership_nif::rw_probe"],
          proof_modules: ["Rw.Properties", "Rw.ModelProperties"],
          required_properties: required
        ]

    result = Lynx.Rust.verify!(workspace, "ownership-nif", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-nif", options).reports

    translated = result.extraction.audit.translated
    refs = result.extraction.audit.references

    for resolver <- [Lynx.Rust.RwLockModels, Lynx.Rust.LockModels, Lynx.Rust.GuardModels] do
      matched =
        Enum.filter(translated["fun_decls"], &(&1 && resolver.resolve(&1, translated, refs)))

      refute matched == []

      for function <- matched do
        assert is_nil(
                 resolver.resolve(
                   put_in(function, ["signature", "is_unsafe"], true),
                   translated,
                   refs
                 )
               )

        assert is_nil(
                 resolver.resolve(put_in(function, ["signature", "abi"], "C"), translated, refs)
               )
      end
    end

    drop =
      Enum.find(
        translated["fun_decls"],
        &(&1 && Lynx.Rust.NativeDrops.consuming_function?(&1, translated, refs))
      )

    drop_model = Lynx.Rust.NativeDrops.resolve(drop, translated, refs)

    assert :ok =
             Lynx.Rust.NativeDrops.audit(
               Enum.reject(translated["fun_decls"], &is_nil/1),
               %{drop["def_id"] => drop_model},
               translated,
               refs
             )

    invalid = invalidate_noop(translated)
    refute invalid == translated

    assert {:error, _, _} =
             Lynx.Rust.NativeDrops.audit(
               Enum.reject(invalid["fun_decls"], &is_nil/1),
               %{drop["def_id"] => drop_model},
               invalid,
               refs
             )

    prepared =
      Lynx.Rustler.prepare!(
        common ++
          [
            workspace: workspace,
            package: "ownership-nif",
            root_attribute: "lynx::rwlock",
            only: [rw_checked: 1]
          ]
      )

    assert [
             %{"name" => "rw_checked", "rust_name" => "rw_scope", "arity" => 1, "flags" => 1} =
               binding
           ] =
             prepared.bindings.bindings

    nif_proof =
      File.read!(Path.join(@fixture, "RwLockNifProperties.lean"))
      |> String.replace("__FACADE__", binding["lean_name"])

    File.write!(Path.join(project, "Rw/NifProperties.lean"), nif_proof)

    nif_options =
      common ++
        [
          workspace: workspace,
          package: "ownership-nif",
          root_attribute: "lynx::rwlock",
          only: [rw_checked: 1],
          proof_modules: ["Rw.Properties", "Rw.ModelProperties", "Rw.NifProperties"],
          required_properties: required ++ ~w(Rw.Properties.facade Rw.Properties.adapter_next)
        ]

    prepared = Lynx.Rustler.prepare!(nif_options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, nif_options[:proof_modules],
        required_properties: nif_options[:required_properties]
      )

    export = Path.join(tmp, "rw.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    elixir = Path.join(workspace, "elixir")
    File.mkdir_p!(elixir)
    stub = Path.join(elixir, "native.ex")

    File.write!(
      stub,
      File.read!(Path.join(@fixture, "elixir/native.ex"))
      |> String.replace("LynxOwnershipFixture", "LynxRwLockFixture")
      |> String.replace(
        "\nend\n",
        "\n  def rw_checked(_value), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)

    for value <- [false, true],
        do: assert(apply(LynxRwLockFixture.Native, :rw_checked, [value]) == !value)

    assert_raise ArgumentError, fn -> apply(LynxRwLockFixture.Native, :rw_checked, [7]) end
    [{law_module, beam}] = Code.compile_file(Path.join(@fixture, "elixir/rw_lock_laws.ex"))
    for law <- ~w(flips_true flips_false rejects_integer)a, do: assert(apply(law_module, law, []))
    law_export = Path.join(tmp, "rw-laws.export")
    law_opts = [native: {Lynx.Rustler, nif_options}]
    reports = Lynx.Laws.verify([beam], law_opts ++ [export: law_export])
    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 3
    assert Enum.all?(Lynx.Laws.verify([beam], law_opts), &(&1.status == :ok and &1.cached))

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", law_export] ++ sandbox)

    assert status == 0, output

    for extra <- [
          "private axiom rwTrust : False",
          "private theorem unfinishedRw : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(nif_options)
      end
    end

    File.write!(property, proof)
    wrong = String.replace(proof, "nativeRefCounter := 5", "nativeRefCounter := 4")
    refute wrong == proof
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(nif_options)
    end

    File.write!(property, proof)

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    unrelated_source = File.read!(unrelated)

    unrelated_change =
      String.replace(unrelated_source, "\n    value\n", "\n    value.wrapping_add(1)\n")

    refute unrelated_change == unrelated_source
    File.write!(unrelated, unrelated_change)
    repeated = Lynx.Rustler.prepare!(nif_options)
    assert repeated.extraction.fingerprint == prepared.extraction.fingerprint
    assert Enum.all?(repeated.reports, &(&1.status == :ok and &1.cached))
    File.write!(unrelated, unrelated_source)

    base = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(base)

    changed =
      String.replace(
        original,
        "pub fn toggle(value: &mut bool) {\n    *value = !*value;",
        "pub fn toggle(value: &mut bool) {\n    *value = false;"
      )

    refute changed == original
    File.write!(base, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(nif_options)
    end

    File.write!(base, original)
    assert Enum.all?(Lynx.Rustler.prepare!(nif_options).reports, &(&1.status == :ok))
  end

  defp invalidate_noop(%{"builtin_data" => "NoopDestruct"} = map),
    do: %{map | "builtin_data" => "UnverifiedDestruct"}

  defp invalidate_noop(map) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, invalidate_noop(value)} end)

  defp invalidate_noop(list) when is_list(list), do: Enum.map(list, &invalidate_noop/1)
  defp invalidate_noop(value), do: value
end
