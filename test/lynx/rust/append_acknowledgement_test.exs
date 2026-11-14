defmodule Lynx.Rust.AppendAcknowledgementTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual append acknowledgements imply durability for arbitrary admitted IO scripts", %{
    tmp_dir: tmp
  } do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, [
        "RepeatedRepairProperties",
        "RecoveryScanInvariant",
        "RepairReturnProperties",
        "RepairImageInvariant",
        "RepairAcknowledgement",
        "RepairWriterProperties",
        "AppendAcknowledgement",
        "RepairAppendAcknowledgement",
        "AppendAcknowledgementWitness"
      ])

    modules = ~w(Record.RepairAcknowledgement Record.AppendAcknowledgement
      Record.RepairAppendAcknowledgement Record.AppendAcknowledgementWitness)
    properties = ~w(Record.RepairAcknowledgement.synchronize_returns
      Record.AppendAcknowledgement.append_returns
      Record.AppendAcknowledgement.append_run_acknowledges
      Record.RepairAppendAcknowledgement.repair_append_returns
      Record.RepairAppendAcknowledgement.repair_append_run_acknowledges
      Record.RepairAppendAcknowledgement.repair_append_twice
      Record.RepairAppendAcknowledgement.acknowledged_crash_retry
      Record.AppendAcknowledgementWitness.full_acknowledges
      Record.AppendAcknowledgementWitness.short_rolls_back
      Record.AppendAcknowledgementWitness.repair_acknowledges)

    options =
      base
      |> Keyword.update!(
        :roots,
        &["io_protocol::repair_and_append", "io_protocol::locked_repair_and_append" | &1]
      )
      |> Keyword.put(:proof_modules, modules)
      |> Keyword.put(:required_properties, properties)

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    for property <- properties do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.kind == :rust_implementation and &1.theorem == property)
             )
    end

    for property <- Enum.drop(properties, 1) do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.kind == :cross_crate_contract and &1.theorem == property)
             )
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file = Proofs.file!(result.extraction, modules, required_properties: properties)
    export = Path.join(tmp, "append-acknowledgement.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for {relative, correct, wrong} <- [
          {"Record/AppendAcknowledgement.lean", "else before.visible", "else ByteArray.empty"},
          {"Record/RepairAppendAcknowledgement.lean", "values ++ [value]",
           "values ++ [value,value]"},
          {"Record/AppendAcknowledgementWitness.lean", "accepted false original 6",
           "accepted true original 6"}
        ] do
      path = Path.join(project, relative)
      source = File.read!(path)
      broken = String.replace(source, correct, wrong)
      refute broken == source
      File.write!(path, broken)
      error = assert_raise RuntimeError, fn -> Project.build!(project, modules) end
      assert error.message =~ ".lean:"
      refute error.message =~ "Unknown identifier"
      File.write!(path, source)
    end

    property = Path.join(project, "Record/RepairAppendAcknowledgement.lean")
    source = File.read!(property)

    for extra <- [
          "private axiom uncheckedAppendAck : False",
          "private theorem unfinishedAppendAck : True := by sorry"
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
          {"resize_then_sync(file, start)", "resize_then_sync(file, 0)"},
          {"Ok(()) => io_core::synchronize(file)", "Ok(()) => Ok(())"},
          {"Some(_records) => append_record_or_rollback(file, value)",
           "Some(_records) => Ok(true)"}
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
