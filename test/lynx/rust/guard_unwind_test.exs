defmodule Lynx.Rust.GuardUnwindTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_ownership", __DIR__)
  @tools System.get_env("LYNX_CAPTURED_RUNTIME_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_CAPTURED_RUNTIME_DIR for guard unwind proofs")

  @tag :tmp_dir
  test "cross-crate panic commits borrowed mutation, poisons and releases the guard", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock base app nif),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Guard"))
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    File.ln_s!(packages, Path.join(project, ".lake/packages"))
    property = Path.join(project, "Guard/Properties.lean")
    properties = File.read!(Path.join(@fixture, "GuardProperties.lean"))
    File.write!(property, properties)

    opts = [
      roots: ["ownership_app::local_guard_panic"],
      tools: @tools,
      execution: :runtime,
      unwind: :captured,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Guard.Extraction",
      proof_modules: ["Guard.Properties"],
      required_properties:
        ~w(Guard.Properties.mutate Guard.Properties.run_composes Guard.Properties.run_heap Guard.Properties.local_scope)
    ]

    verify = fn -> Lynx.Rust.verify!(workspace, "ownership-app", opts) end
    result = verify.()
    assert [%{status: :ok}] = result.reports
    assert Enum.any?(result.extraction.native_drops, & &1.unwind)
    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(result.verification.unverified_external_calls, fn call ->
             call.implementation_verified == false and
               String.contains?(call.label, "unlocks and poisons")
           end)

    assert [%{status: :ok, cached: true}] = verify.().reports

    file =
      Lynx.Rust.Proofs.file!(result.extraction, opts[:proof_modules],
        required_properties: opts[:required_properties]
      )

    export = Path.join(tmp, "guard.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom guardTrust : False",
          "private theorem unfinishedGuard : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")
      assert_raise RuntimeError, ~r/Rust properties or proof audit failed/, verify
    end

    File.write!(property, properties)

    wrong = String.replace(properties, "poisoned || !accepted", "poisoned")
    refute wrong == properties
    File.write!(property, wrong)
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(property, properties)

    source = Path.join(workspace, "base/src/lib.rs")
    original = File.read!(source)
    changed = String.replace(original, "*value = !*value;", "*value = *value;")
    refute original == changed
    File.write!(source, changed)
    assert_raise RuntimeError, ~r/native Lean project command failed/, verify
    File.write!(source, original)
    assert [%{status: :ok}] = verify.().reports

    assert_raise ArgumentError, ~r/unknown Rust verification option: external_calls/, fn ->
      Lynx.Rust.verify!(
        workspace,
        "ownership-app",
        Keyword.put(opts, :external_calls, [:captured_unwind_drops])
      )
    end

    assert_raise ArgumentError, ~r/compiler-managed/, fn ->
      Lynx.Rust.Extraction.run!(nil, nil, [], nil, nil, external_calls: [:captured_unwind_drops])
    end

    assert_raise ArgumentError, ~r/reserved compiler unwind namespace/, fn ->
      Lynx.Rust.NativeUnwindDrops.prepare!(result.extraction.audit.document)
    end
  end
end
