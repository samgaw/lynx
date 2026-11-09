defmodule Lynx.Rust.GuardDriverTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "cancelling-futures-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned cancelling-futures backend")

  @tag :tmp_dir
  test "composes actual guard-holding future drivers and scope-exit cancellation", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "GuardDriver"))
    property = Path.join(project, "GuardDriver/Contracts.lean")
    original = File.read!(Path.join(@fixture, "NativeGuardDriver.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::finish_guarded", "effects_native::cancel_guarded"],
      futures: :cancelling,
      owned_drops: true,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "GuardDriver.Extraction",
      proof_modules: ["GuardDriver.Contracts"],
      required_properties:
        Enum.map(
          ~w(increment_spec callee_contract first_poll resumed_poll saved_drop completed_drop finish_contract cancel_contract),
          &("GuardDriver.Contracts." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    for theorem <- ~w(finish_contract cancel_contract) do
      assert Enum.any?(result.verification.guarantees, fn guarantee ->
               guarantee.theorem == "GuardDriver.Contracts." <> theorem &&
                 "GuardDriver.Contracts.first_poll" in guarantee.contracts_used
             end)
    end

    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    file = Proofs.file!(result.extraction, options[:proof_modules], options)
    export = Path.join(tmp, "guard-driver.export")

    assert [%{status: :ok, cached: false}] =
             Lynx.Commands.verify!(project, [file], export: export)

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom driverTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, options[:proof_modules])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    wrong =
      String.replace(
        original,
        "Result.ok (true, NativeTaskContext",
        "Result.ok (false, NativeTaskContext"
      )

    refute wrong == original
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, options[:proof_modules])
    end

    File.write!(property, original)
    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)
    # Preserve a valid coroutine and both drivers, but violate their actual
    # cross-crate transition. A previous successful proof must not be reused.
    changed =
      String.replace(
        source,
        "let changed = effects_core::increment_guard(&mut guard, amount);",
        "let changed = effects_core::increment_guard(&mut guard, 0);",
        global: false
      )

    refute changed == source
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(native, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
