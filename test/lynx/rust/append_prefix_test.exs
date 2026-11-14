defmodule Lynx.Rust.AppendPrefixTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual Rust prefixes preserve old acknowledgements before success and through failures",
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
        "RecoveryPrefixInvariant",
        "RepairPrefixInvariant",
        "RepairAppendPrefixInvariant",
        "AppendPrefixWitness"
      ])

    modules = ~w(Record.AppendPrefixInvariant Record.RepairAppendPrefixInvariant
      Record.AppendAcknowledgementWitness Record.AppendPrefixWitness)
    properties = ~w(Record.AppendPrefixInvariant.append_invariant
      Record.AppendPrefixInvariant.append_prefix_invariant
      Record.AppendPrefixInvariant.recover_prefix_image
      Record.AppendPrefixInvariant.recover_after_append_prefix
      Record.RepairAppendPrefixInvariant.repair_append_invariant
      Record.RepairAppendPrefixInvariant.repair_append_prefix_invariant
      Record.RepairAppendPrefixInvariant.recover_after_repair_append_prefix
      Record.AppendAcknowledgementWitness.full_acknowledges
      Record.AppendAcknowledgementWitness.short_rolls_back
      Record.AppendAcknowledgementWitness.repair_acknowledges
      Record.AppendPrefixWitness.resize_error_retains_tail
      Record.AppendPrefixWitness.sync_error_can_persist_record
      Record.AppendPrefixWitness.blocked_rollback_retains_tail)

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
    export = Path.join(tmp, "append-prefix.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for {relative, correct, wrong} <- [
          {"Record/AppendPrefixInvariant.lean", "(afterHead : head.size ≤ position)",
           "(afterHead : position ≤ head.size)"},
          {"Record/RepairAppendPrefixInvariant.lean", "Vec.from values", "Vec.from []"},
          {"Record/AppendPrefixWitness.lean", "failed partialImage partialImage 6",
           "failed original original 6"},
          {"Record/AppendPrefixWitness.lean", "| .deadlock => effects", "| .ok _ => effects"}
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

    property = Path.join(project, "Record/RepairAppendPrefixInvariant.lean")
    source = File.read!(property)

    for extra <- [
          "private axiom uncheckedAppendPrefix : False",
          "private theorem unfinishedAppendPrefix : True := by sorry"
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
          {"pub fn append_record_or_rollback(file: &mut File, value: u16) -> io::Result<bool> {\n    match io_core::seek_from(file, std::io::SeekFrom::End(0))",
           "pub fn append_record_or_rollback(file: &mut File, value: u16) -> io::Result<bool> {\n    match io_core::seek_from(file, std::io::SeekFrom::Start(0))"},
          {"resize_then_sync(file, start)", "resize_then_sync(file, 0)"}
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
