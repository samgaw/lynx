defmodule Lynx.Rust.LockedPrefixTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual Rust guarded repair preserves identities and prefixes across all result branches",
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
        "RecoveryVisibleFrame",
        "RepairVisibleInvariant",
        "FileReturnIdentity",
        "LockedPrefixInvariant",
        "LockedPrefixWitness",
        "UnsyncedRepairWitness"
      ])

    modules =
      ~w(Record.RecoveryVisibleFrame Record.RepairVisibleInvariant Record.FileReturnIdentity
      Record.LockedPrefixInvariant Record.LockedPrefixWitness Record.UnsyncedRepairWitness)

    properties = ~w(Record.FileReturnIdentity.recover_returns
      Record.FileReturnIdentity.repair_returns
      Record.FileReturnIdentity.append_returns
      Record.FileReturnIdentity.repair_append_returns
      Record.LockedPrefixInvariant.critical_invariant
      Record.LockedPrefixInvariant.critical_returns
      Record.LockedPrefixInvariant.body_excludes_peer
      Record.LockedPrefixInvariant.critical_prefix
      Record.LockedPrefixInvariant.crash_recovery
      Record.LockedPrefixWitness.poisoned_success
      Record.LockedPrefixWitness.read_error_releases
      Record.LockedPrefixWitness.sync_error_releases
      Record.LockedPrefixWitness.capped_releases
      Record.LockedPrefixWitness.blocked_keeps_guard
      Record.RecoveryVisibleFrame.word_returns Record.RecoveryVisibleFrame.record_returns
      Record.RecoveryVisibleFrame.recover_returns_prefix Record.RecoveryVisibleFrame.recover_returns
      Record.RepairVisibleInvariant.repair_returns_prefix Record.RepairVisibleInvariant.repair_log_invariant
      Record.RepairVisibleInvariant.repair_append_invariant
      Record.FileReturnIdentity.repair_returns_general Record.FileReturnIdentity.repair_append_returns_general
      Record.LockedPrefixInvariant.critical_invariant_general Record.LockedPrefixInvariant.critical_returns_general
      Record.UnsyncedRepairWitness.shorter_durable_success Record.UnsyncedRepairWitness.longer_durable_success
      Record.UnsyncedRepairWitness.longer_durable_sync_error Record.UnsyncedRepairWitness.shorter_durable_read_error
      Record.UnsyncedRepairWitness.longer_durable_blocked)

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
    export = Path.join(tmp, "locked-prefix.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for {relative, correct, wrong} <- [
          {"Record/FileReturnIdentity.lean", "returnedFile = file",
           "returnedFile = ⟨file.id + 1⟩"},
          {"Record/LockedPrefixInvariant.lean", "Vec.from values", "Vec.from []"},
          {"Record/LockedPrefixWitness.lean", "effects true false visible durable position",
           "effects true true visible durable position"},
          {"Record/LockedPrefixWitness.lean", "(failed repaired image 12)",
           "(failed image image 12)"},
          {"Record/LockedPrefixWitness.lean", "effects true true repaired image 12",
           "effects true false repaired image 12"},
          {"Record/RecoveryVisibleFrame.lean", "after.position = before.position + 4",
           "after.position = before.position + 3"},
          {"Record/RepairVisibleInvariant.lean", "returned.val = values ++ suffix",
           "returned.val = values ++ [0#u16] ++ suffix"},
          {"Record/UnsyncedRepairWitness.lean", "failed repaired longDurable 12",
           "failed repaired repaired 12"},
          {"Record/LockedPrefixWitness.lean", "env.nativeRefCounter == 10",
           "env.nativeRefCounter == 9"}
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

    property = Path.join(project, "Record/LockedPrefixInvariant.lean")
    source = File.read!(property)

    for extra <- [
          "private axiom uncheckedLockedPrefix : False",
          "private theorem unfinishedLockedPrefix : True := by sorry"
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
          {"repair_and_append(&mut guard, max_records, value)",
           "repair_and_append(&mut guard, max_records, !value)"},
          {"repair_and_append(&mut guard, max_records, value)", "Ok(false)"},
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
