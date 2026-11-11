defmodule Lynx.Rustler.TryRwTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR for nonblocking read/write lock proofs")

  @tag :tmp_dir
  test "nonblocking critical sections preserve rejected state and compose through a NIF", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    native = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      native,
      String.replace(File.read!(native), "LynxOwnershipFixture", "LynxTryRwFixture")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "TryRw"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../rust_workspace/proofs/.lake/packages", @fixture),
      Path.join(project, ".lake/packages")
    )

    property = Path.join(project, "TryRw/Properties.lean")
    proof = File.read!(Path.join(@fixture, "TryRwLockProperties.lean"))
    File.write!(property, proof)

    required =
      Enum.map(
        ~w(toggle held shared available cycle queued invalid),
        &("TryRw.Properties." <> &1)
      )

    common = [
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      cargo: [features: ["try-rwlock"]],
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "TryRw.Extraction",
      proof_modules: ["TryRw.Properties"],
      required_properties: required
    ]

    internal = common ++ [roots: ["ownership_app::try_rw_cycle"]]
    result = Lynx.Rust.verify!(workspace, "ownership-nif", internal)
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "ownership-nif", internal).reports

    options =
      common ++
        [
          workspace: workspace,
          package: "ownership-nif",
          root_attribute: "lynx::try_rwlock",
          only: [try_rw_checked: 1]
        ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "try_rw_checked",
               "rust_name" => "try_rw_request",
               "arity" => 1,
               "flags" => 0
             } =
               binding
           ] = prepared.bindings.bindings

    nif = File.read!(Path.join(@fixture, "TryRwLockNifProperties.lean"))

    File.write!(
      Path.join(project, "TryRw/NifProperties.lean"),
      String.replace(nif, "__FACADE__", binding["lean_name"])
    )

    proofs = ["TryRw.Properties", "TryRw.NifProperties"]
    required = required ++ ~w(TryRw.Properties.facade TryRw.Properties.adapter_next)
    options = Keyword.merge(options, proof_modules: proofs, required_properties: required)
    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :nif_adapter))

    assert Enum.any?(
             prepared.verification.unverified_external_calls,
             &(not &1.implementation_verified and String.contains?(&1.label, "WouldBlock"))
           )

    audit = prepared.extraction.audit

    functions =
      Enum.filter(audit.translated["fun_decls"], fn f ->
        f &&
          match?(
            %{native_try_lock_type: id} when is_integer(id),
            Lynx.Rust.LockModels.resolve(f, audit.translated, audit.references)
          )
      end)

    assert Enum.sort(
             Enum.map(functions, fn function ->
               Lynx.Rust.LockModels.resolve(function, audit.translated, audit.references).native_guard_kind
             end)
           ) == [:rw_read, :rw_write]

    for function <- functions do
      assert is_nil(
               Lynx.Rust.LockModels.resolve(
                 put_in(function, ["signature", "abi"], "C"),
                 audit.translated,
                 audit.references
               )
             )

      assert is_nil(
               Lynx.Rust.LockModels.resolve(
                 put_in(function, ["signature", "is_unsafe"], true),
                 audit.translated,
                 audit.references
               )
             )

      model = Lynx.Rust.LockModels.resolve(function, audit.translated, audit.references)

      forged =
        update_in(audit.translated, ["type_decls"], fn types ->
          Enum.map(types, fn
            %{"def_id" => id} = type when id == model.native_try_lock_type ->
              put_in(type, ["kind", "Enum", Access.at(1), "name"], "Other")

            type ->
              type
          end)
        end)

      assert is_nil(Lynx.Rust.LockModels.resolve(function, forged, audit.references))
    end

    file = Lynx.Rust.Proofs.file!(prepared.extraction, proofs, required_properties: required)
    export = Path.join(tmp, "try-rwlock.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libownership_nif.so"))
    File.mkdir_p!(Path.join(workspace, "elixir"))
    stub = Path.join(workspace, "elixir/native.ex")

    File.write!(
      stub,
      File.read!(Path.join(@fixture, "elixir/native.ex"))
      |> String.replace("LynxOwnershipFixture", "LynxTryRwFixture")
      |> String.replace(
        "\nend\n",
        "\n  def try_rw_checked(_value), do: :erlang.nif_error(:not_loaded)\nend\n"
      )
    )

    Code.compile_file(stub)

    for value <- [false, true],
        do:
          assert(
            apply(LynxTryRwFixture.Native, :try_rw_checked, [value]) ==
              {false, false, true, not value}
          )

    assert_raise ArgumentError, fn -> apply(LynxTryRwFixture.Native, :try_rw_checked, [7]) end
    [{module, beam}] = Code.compile_file(Path.join(@fixture, "elixir/try_rwlock_laws.ex"))
    for law <- ~w(flips_false flips_true rejects_integer)a, do: assert(apply(module, law, []))
    law_export = Path.join(tmp, "try-rwlock-laws.export")
    law_options = [native: {Lynx.Rustler, options}]
    reports = Lynx.Laws.verify([beam], law_options ++ [export: law_export])
    errors = for report <- reports, report.status != :ok, do: report.diagnostics
    assert errors == [], inspect(errors, limit: :infinity)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 3

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", law_export] ++ sandbox)

    assert status == 0, output
    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))

    for extra <- [
          "private axiom tryLockTrust : False",
          "private theorem unfinishedTryRw : True := by sorry"
        ] do
      File.write!(property, proof <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, proof)
    wrong = String.replace(proof, "nativeRefCounter := 5", "nativeRefCounter := 4")
    refute wrong == proof
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property, proof)
    base = Path.join(workspace, "base/src/lib.rs")
    source = File.read!(base)

    changed =
      String.replace(
        source,
        "TryLockError::WouldBlock) => return false",
        "TryLockError::WouldBlock) => return true"
      )

    refute changed == source
    File.write!(base, changed)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert error.message =~ "TryRw.Properties"
    File.write!(base, source)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
