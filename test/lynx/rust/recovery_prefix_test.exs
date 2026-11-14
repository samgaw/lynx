defmodule Lynx.Rust.RecoveryPrefixTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual Rust recovery and repair retain acknowledged prefixes through arbitrary suffixes",
       %{
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
        "AppendAcknowledgementWitness",
        "EncodedPrefixRecovery",
        "AppendPrefixInvariant",
        "RecoveryFrame",
        "RepairPrefixReturn",
        "RecoveryPrefixWitness"
      ])

    modules = ~w(Record.RecoveryFrame Record.RepairPrefixReturn Record.RecoveryPrefixWitness)
    properties = ~w(Record.RecoveryFrame.word_returns
      Record.RecoveryFrame.record_returns
      Record.RecoveryFrame.recover_returns_prefix
      Record.RepairPrefixReturn.repair_returns_prefix
      Record.RecoveryPrefixWitness.scans_extra_record
      Record.RecoveryPrefixWitness.repairs_arbitrary_suffix
      Record.RecoveryPrefixWitness.capped_retains_suffix)

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

    for property <- properties do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.kind == :cross_crate_contract and &1.theorem == property)
             )
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file = Proofs.file!(result.extraction, modules, required_properties: properties)
    export = Path.join(tmp, "recovery-prefix.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for {relative, correct, wrong} <- [
          {"Record/RecoveryFrame.lean", "after.position = before.position + 4",
           "after.position = before.position + 3"},
          {"Record/RecoveryPrefixWitness.lean", "values.val == [13#u16,19#u16]",
           "values.val == [13#u16]"},
          {"Record/RecoveryPrefixWitness.lean", "state.position == 12", "state.position == 8"},
          {"Record/RecoveryPrefixWitness.lean", "result.isNone", "result.isSome"}
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

    property = Path.join(project, "Record/RepairPrefixReturn.lean")
    source = File.read!(property)

    for extra <- [
          "private axiom uncheckedRecoveryPrefix : False",
          "private theorem unfinishedRecoveryPrefix : True := by sorry"
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
          {"Ok(Some(value)) => values.push(value)", "Ok(Some(value)) => values.push(!value)"},
          {"resize_then_sync(file, valid_bytes)", "resize_then_sync(file, 0)"}
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
