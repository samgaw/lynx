defmodule Lynx.Rustler.CompareExchangeTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RESOURCE_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_CAPTURED_RESOURCE_DIR for atomic compare exchange NIF laws")

  @tag :tmp_dir
  test "verifies conditional resource updates and competing NIF transitions", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")
    File.write!(rust, String.replace(File.read!(rust), "LynxAtomicFixture", "LynxCompareFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Compare"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    common = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      root_attribute: "lynx::compare",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Compare.Extraction",
      only: [atomic_new: 1, atomic_read: 1, atomic_replace: 3]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    core_properties =
      File.read!(Path.join(@fixture, "CompareProperties.lean"))
      |> String.replace("Atomic.Compare.Funs", "Compare.Extraction.Funs")
      |> String.replace("Atomic.CompareProperties", "Compare.Properties")
      |> String.replace("Lynx atomic_analysis", "Lynx atomic_nif")
      |> String.replace("try_set", "atomic_analysis.try_set")

    facade =
      Enum.reduce(
        ~w(NEW READ REPLACE),
        File.read!(Path.join(@fixture, "CompareNifProperties.lean")),
        fn placeholder, source ->
          binding =
            Enum.find(
              prepared.bindings.bindings,
              &(&1["name"] == "atomic_" <> String.downcase(placeholder))
            )

          String.replace(source, "__#{placeholder}__", binding["lean_name"])
        end
      )

    properties =
      String.replace(
        core_properties,
        "end Compare.Properties",
        facade <> "\nend Compare.Properties"
      )

    property = Path.join(project, "Compare/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Compare.Properties"],
          required_properties:
            Enum.map(
              ~w(contract matched mismatch composed_match composed_mismatch unavailable every_interleaving every_run resource_contract facade_new facade_read facade_replace),
              &("Compare.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.map(prepared.bindings.bindings, &{&1["name"], &1["arity"], &1["flags"]})
           |> Enum.sort() == [
             {"atomic_new", 1, 0},
             {"atomic_read", 1, 0},
             {"atomic_replace", 3, 1}
           ]

    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    native_source =
      File.read!(Path.join(workspace, "elixir/native.ex"))
      |> String.replace("LynxAtomicFixture", "LynxCompareFixture")

    Code.compile_string(native_source, Path.join(workspace, "elixir/native.ex"))
    native = LynxCompareFixture.Native
    resource = apply(native, :atomic_new, [7])
    assert apply(native, :atomic_replace, [resource, 7, 11]) == {true, 7}
    assert apply(native, :atomic_replace, [resource, 7, 99]) == {false, 11}
    assert apply(native, :atomic_read, [resource]) == 11

    for invalid <- [-1, 18_446_744_073_709_551_616, false] do
      assert_raise ArgumentError, fn ->
        apply(native, :atomic_replace, [resource, 11, invalid])
      end

      assert apply(native, :atomic_read, [resource]) == 11
    end

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/compare_laws.ex"))

    for law <- ~w(matched_update mismatch_preserves decoder_cleanup competing_transitions)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "compare-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: export,
        options: [maxHeartbeats: 16_000_000, maxRecDepth: 8192]
      )

    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 4
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    file =
      Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    for invalid <- [
          "private axiom uncheckedCompare : False",
          "private theorem unfinishedCompare : False := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      Lynx.Rust.Project.build!(project, ["Compare.Properties"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(property, properties)

    changed =
      String.replace(
        File.read!(rust),
        "try_set(&resource.state, expected, replacement)",
        "try_set(&resource.state, replacement, expected)"
      )

    assert changed != File.read!(rust)
    File.write!(rust, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
