defmodule Lynx.Rust.RepairImageInvariantTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual Rust repair preserves arbitrary logs at every runtime prefix", %{tmp_dir: tmp} do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, [
        "RepeatedRepairProperties",
        "RecoveryScanInvariant",
        "RepairReturnProperties",
        "RepairImageInvariant",
        "RepairImageCrash",
        "RepairAcknowledgement"
      ])

    properties =
      ~w(Record.RepairReturnProperties.recover_returns
      Record.RepairImageInvariant.resize_then_sync_invariant
      Record.RepairImageInvariant.repair_log_invariant
      Record.RepairImageInvariant.repair_prefix_invariant
      Record.RepairImageCrash.recover_after_repair_crash
      Record.RepairAcknowledgement.resize_then_sync_returns
      Record.RepairAcknowledgement.repair_returns
      Record.RepairAcknowledgement.repair_run_acknowledges
      Record.RepairAcknowledgement.acknowledged_crash_image
      Record.RepairAcknowledgement.repair_twice
      Record.ResizeProperties.repair_default
      Record.ResizeProperties.resize_sync_failure)

    modules =
      ~w(Record.ResizeProperties Record.RepairReturnProperties Record.RepairImageInvariant Record.RepairImageCrash Record.RepairAcknowledgement)

    options =
      base
      |> Keyword.put(:proof_modules, modules)
      |> Keyword.put(:required_properties, properties)

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    for property <- properties do
      assert Enum.any?(result.verification.guarantees, fn evidence ->
               evidence.kind == :rust_implementation and evidence.theorem == property
             end)
    end

    assert Enum.any?(result.verification.guarantees, fn evidence ->
             evidence.kind == :cross_crate_contract and
               evidence.theorem == "Record.RepairImageInvariant.repair_log_invariant"
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "repair-image.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    acknowledgement = Path.join(project, "Record/RepairAcknowledgement.lean")
    acknowledgement_source = File.read!(acknowledgement)

    false_image =
      String.replace(
        acknowledgement_source,
        "image.bytes = disk (logBytes values)",
        "image.bytes = disk (logBytes values.reverse)"
      )

    refute false_image == acknowledgement_source
    File.write!(acknowledgement, false_image)
    error = assert_raise RuntimeError, fn -> Project.build!(project, modules) end
    assert error.message =~ "RepairAcknowledgement.lean:"
    refute error.message =~ "Unknown identifier"
    File.write!(acknowledgement, acknowledgement_source)

    return_property = Path.join(project, "Record/RepairReturnProperties.lean")
    return_source = File.read!(return_property)

    wrong_return =
      String.replace(return_source, "returned.val = values)", "returned.val = values.reverse)")

    refute wrong_return == return_source
    File.write!(return_property, wrong_return)
    error = assert_raise RuntimeError, fn -> Project.build!(project, modules) end
    assert error.message =~ "RepairReturnProperties.lean:"
    refute error.message =~ "Unknown identifier"
    File.write!(return_property, return_source)

    property = Path.join(project, "Record/RepairImageCrash.lean")
    source = File.read!(property)
    wrong = String.replace(source, "Vec.from values", "Vec.from values.reverse")
    refute wrong == source
    File.write!(property, wrong)
    error = assert_raise RuntimeError, fn -> Project.build!(project, options[:proof_modules]) end
    assert error.message =~ "RepairImageCrash.lean:"
    refute error.message =~ "Unknown identifier"

    for extra <- [
          "private axiom uncheckedRepair : False",
          "private theorem unfinishedRepair : True := by sorry"
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
          {"Ok(Some(value)) => values.push(value)", "Ok(Some(value)) => values.push(0)"},
          {"checked_mul(4)", "checked_mul(3)"},
          {"Ok(()) => io_core::synchronize(file)", "Ok(()) => Ok(())"},
          {"Err(error) => Err(error),\n                Ok(()) => Ok(Some(values))",
           "Err(_error) => Ok(Some(values)),\n                Ok(()) => Ok(Some(values))"}
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
