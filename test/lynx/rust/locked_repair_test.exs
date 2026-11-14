defmodule Lynx.Rust.LockedRepairTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 2_400_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "overlapping actual Rust repairs preserve records at every runtime prefix", %{tmp_dir: tmp} do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, [
        "RepeatedRepairProperties",
        "RecoveryScanInvariant",
        "RepairReturnProperties",
        "RepairImageInvariant",
        "RepairAcknowledgement",
        "LockedRepairProperties",
        "ConcurrentRepairInvariant",
        "ConcurrentRepairRecovery"
      ])

    modules =
      ~w(Record.LockedRepairProperties Record.ConcurrentRepairInvariant Record.ConcurrentRepairRecovery)

    properties = ~w(Record.LockedRepairProperties.critical_contract
      Record.LockedRepairProperties.body_excludes_peer
      Record.ConcurrentRepairRecovery.recover_after_prefix
      Record.ConcurrentRepairRecovery.terminal_recovery)

    options =
      base
      |> Keyword.update!(:roots, &["io_protocol::locked_repair" | &1])
      |> Keyword.put(:proof_modules, modules)
      |> Keyword.put(:required_properties, properties)

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    for property <- properties do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.kind == :cross_crate_contract and &1.theorem == property)
             )
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file = Proofs.file!(result.extraction, modules, required_properties: properties)
    export = Path.join(tmp, "locked-repair.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Record/ConcurrentRepairRecovery.lean")
    source = File.read!(property)

    for {correct, wrong} <- [
          {"Vec.from [13#u16]", "Vec.from [14#u16]"},
          {"image.bytes = complete ∧", "image.bytes = torn ∧"}
        ] do
      broken = String.replace(source, correct, wrong)
      refute broken == source
      File.write!(property, broken)
      error = assert_raise RuntimeError, fn -> Project.build!(project, modules) end
      assert error.message =~ "ConcurrentRepairRecovery.lean:"
      refute error.message =~ "Unknown identifier"
    end

    for extra <- [
          "private axiom uncheckedConcurrentRepair : False",
          "private theorem unfinishedConcurrentRepair : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      error =
        assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

      assert error.message =~ "audit"
    end

    File.write!(property, source)

    rust = Path.join(workspace, "protocol/src/lib.rs")
    original = File.read!(rust)

    for {correct, wrong} <- [
          {"repair_log(&mut guard, max_records)", "repair_log(&mut guard, 0)"},
          {"Ok(()) => io_core::synchronize(file)", "Ok(()) => Ok(())"}
        ] do
      broken = String.replace(original, correct, wrong)
      refute broken == original
      File.write!(rust, broken)

      error =
        assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

      assert error.message =~ ~r/Record\/[^\s]+\.lean:\d+:/
      refute error.message =~ "Unknown identifier"
      File.write!(rust, original)
      assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
    end
  end
end
