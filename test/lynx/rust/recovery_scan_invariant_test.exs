defmodule Lynx.Rust.RecoveryScanInvariantTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "actual Rust scans preserve arbitrary logs at every runtime prefix", %{tmp_dir: tmp} do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, [
        "RepeatedRepairProperties",
        "RecoveryScanInvariant",
        "RecoveryScanCrash"
      ])

    properties =
      ~w(Record.RecoveryScanInvariant.read_once_invariant
      Record.RecoveryScanInvariant.record_invariant
      Record.RecoveryScanInvariant.recover_log_invariant
      Record.RecoveryScanInvariant.recover_prefix_invariant
      Record.RecoveryScanCrash.recover_after_scan_crash)

    options =
      base
      |> Keyword.put(:proof_modules, ["Record.RecoveryScanInvariant", "Record.RecoveryScanCrash"])
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
               evidence.theorem == "Record.RecoveryScanInvariant.recover_log_invariant"
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "recovery-scan.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Record/RecoveryScanCrash.lean")
    source = File.read!(property)
    wrong = String.replace(source, "Vec.from values", "Vec.from values.reverse")
    refute wrong == source
    File.write!(property, wrong)
    error = assert_raise RuntimeError, fn -> Project.build!(project, options[:proof_modules]) end
    assert error.message =~ "RecoveryScanCrash.lean:"
    refute error.message =~ "Unknown identifier"

    for extra <- [
          "private axiom uncheckedScan : False",
          "private theorem unfinishedScan : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      error =
        assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

      assert error.message =~ "audit"
    end

    File.write!(property, source)
    rust = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(rust)
    broken = String.replace(original, "    file.read(bytes)", "    file.write(bytes)")
    refute broken == original
    File.write!(rust, broken)

    error =
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

    assert error.message =~ "Record/ReadProperties.lean:"
    refute error.message =~ "Unknown identifier"
    File.write!(rust, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
