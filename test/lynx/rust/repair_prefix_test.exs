defmodule Lynx.Rust.RepairPrefixTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual Rust repair prefixes preserve acknowledgements through arbitrary suffixes and failures",
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
        "RecoveryPrefixWitness",
        "RecoveryPrefixInvariant",
        "RepairPrefixInvariant",
        "RepairAppendPrefixInvariant",
        "RepairPrefixWitness"
      ])

    modules = ~w(Record.RecoveryPrefixInvariant Record.RepairPrefixInvariant
      Record.RepairAppendPrefixInvariant Record.RepairPrefixWitness)
    properties = ~w(Record.RecoveryPrefixInvariant.read_once_invariant
      Record.RecoveryPrefixInvariant.record_invariant
      Record.RecoveryPrefixInvariant.recover_log_invariant
      Record.RepairPrefixInvariant.repair_log_invariant
      Record.RepairPrefixInvariant.repair_prefix_invariant
      Record.RepairPrefixInvariant.recover_after_repair_prefix
      Record.RepairAppendPrefixInvariant.repair_append_invariant
      Record.RepairAppendPrefixInvariant.repair_append_prefix_invariant
      Record.RepairAppendPrefixInvariant.recover_after_repair_append_prefix
      Record.RepairPrefixWitness.read_error_retains_cursor
      Record.RepairPrefixWitness.resize_error_retains_suffix
      Record.RepairPrefixWitness.sync_error_persists_resize
      Record.RepairPrefixWitness.blocked_before_resize
      Record.RepairPrefixWitness.blocked_before_sync)

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

    for property <- properties -- ~w(Record.RecoveryPrefixInvariant.read_once_invariant) do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.kind == :cross_crate_contract and &1.theorem == property)
             )
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file = Proofs.file!(result.extraction, modules, required_properties: properties)
    export = Path.join(tmp, "repair-prefix.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for {relative, correct, wrong} <- [
          {"Record/RepairPrefixInvariant.lean", "Vec.from values", "Vec.from []"},
          {"Record/RepairPrefixWitness.lean", "(failed image image 5)", "(failed image image 4)"},
          {"Record/RepairPrefixWitness.lean", "(failed image image 12)",
           "(failed repaired repaired 12)"},
          {"Record/RepairPrefixWitness.lean", "(blocked repaired image)",
           "(blocked repaired repaired)"},
          {"Record/RepairPrefixWitness.lean", "| .deadlock =>", "| .ok _ =>"}
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

    property = Path.join(project, "Record/RepairPrefixInvariant.lean")
    source = File.read!(property)

    for extra <- [
          "private axiom uncheckedRepairPrefix : False",
          "private theorem unfinishedRepairPrefix : True := by sorry"
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
          {"resize_then_sync(file, valid_bytes)", "resize_then_sync(file, 0)"},
          {"if values.len() == max_records {", "if false {"}
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
