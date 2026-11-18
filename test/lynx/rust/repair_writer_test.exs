defmodule Lynx.Rust.RepairWriterTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual repairing Rust writers preserve every observed acknowledgement through crashes", %{
    tmp_dir: tmp
  } do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare_repair_writer!(tmp, @tools, [
        "RepeatedRepairProperties",
        "RecoveryScanInvariant",
        "RepairReturnProperties",
        "RepairImageInvariant",
        "RepairAcknowledgement",
        "RepairWriterProperties",
        "RepairWriterObserver",
        "ConcurrentRepairWriterInvariant",
        "EncodedPrefixRecovery",
        "ConcurrentRepairWriterRecovery",
        "NamedJournalCrash",
        "NamedConcurrentRepairWriter",
        "NamedConcurrentWriterCrash",
        "SharedReadProperties",
        "NamedConcurrentWriterRecovery"
      ])

    modules =
      ~w(Record.RepairWriterProperties Record.RepairWriterObserver
      Record.ConcurrentRepairWriterInvariant Record.EncodedPrefixRecovery
      Record.ConcurrentRepairWriterRecovery Record.NamedJournalCrash
      Record.NamedConcurrentRepairWriter Record.NamedConcurrentWriterCrash
      Record.SharedReadProperties Record.NamedConcurrentWriterRecovery)

    properties = ~w(Record.RepairWriterProperties.repair_append_contract
      Record.RepairWriterProperties.critical_contract
      Record.ConcurrentRepairWriterInvariant.prefixes_checked
      Record.EncodedPrefixRecovery.recover_prefix
      Record.EncodedPrefixRecovery.restart_prefix
      Record.ConcurrentRepairWriterRecovery.recover_acknowledgements
      Record.ConcurrentRepairWriterRecovery.terminal_recovery
      Record.NamedConcurrentRepairWriter.named_prefixes_checked
      Record.NamedConcurrentWriterCrash.prefix_crash
      Record.NamedConcurrentWriterCrash.terminal_crash
      Record.NamedConcurrentWriterRecovery.recover_acknowledgements)

    options =
      base
      |> Keyword.update!(:roots, &["io_core::open_readonly" | &1])
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

    recovery = "Record.NamedConcurrentWriterRecovery.recover_acknowledgements"

    for implementation <- ~w(io_protocol::locked_repair_and_append io_core::open_readonly
          io_protocol::recover_log) do
      assert Enum.any?(result.verification.guarantees, fn evidence ->
               evidence.kind == :rust_implementation and evidence.theorem == recovery and
                 evidence.rust_name == implementation
             end)
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file = Proofs.file!(result.extraction, modules, required_properties: properties)
    export = Path.join(tmp, "repair-writer.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Record/ConcurrentRepairWriterRecovery.lean")
    source = File.read!(property)

    try do
      for {correct, wrong} <- [
            {"13#u16 ∈ values", "14#u16 ∈ values"},
            {"image.bytes = disk (logBytes values)", "image.bytes = torn"}
          ] do
        broken = String.replace(source, correct, wrong)
        refute broken == source
        File.write!(property, broken)
        error = assert_raise RuntimeError, fn -> Project.build!(project, modules) end
        assert error.message =~ "ConcurrentRepairWriterRecovery.lean:"
        refute error.message =~ "Unknown identifier"
      end
    after
      File.write!(property, source)
    end

    named = Path.join(project, "Record/NamedConcurrentWriterRecovery.lean")
    original_named = File.read!(named)

    try do
      false_record = String.replace(original_named, "13#u16 ∈ values", "14#u16 ∈ values")
      refute false_record == original_named
      File.write!(named, false_record)

      assert_raise RuntimeError, ~r/NamedConcurrentWriterRecovery\.lean:\d+:/, fn ->
        Project.build!(project, ["Record.NamedConcurrentWriterRecovery"])
      end
    after
      File.write!(named, original_named)
    end

    for extra <- [
          "private axiom uncheckedRepairWriter : False",
          "private theorem unfinishedRepairWriter : True := by sorry"
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
           "repair_and_append(&mut guard, 0, value)"},
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
