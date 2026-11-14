defmodule Lynx.Rust.RepairInvariantTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 1_200_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "checks actual Rust repair at every reachable prefix", %{tmp_dir: tmp} do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, [
        "RepeatedRepairProperties",
        "RepairInvariantProperties"
      ])

    properties =
      ~w(old_image_checked truncated_image_checked padded_image_checked recover_after_prefix)

    options =
      base
      |> Keyword.put(:proof_modules, ["Record.RepairInvariantProperties"])
      |> Keyword.put(
        :required_properties,
        Enum.map(properties, &("Record.RepairInvariantProperties." <> &1))
      )

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    for property <- properties do
      assert Enum.any?(
               result.verification.guarantees,
               &(&1.theorem == "Record.RepairInvariantProperties." <> property)
             )
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "repair-invariant.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    property = Path.join(project, "Record/RepairInvariantProperties.lean")
    source = File.read!(property)
    wrong = String.replace(source, "Vec.from [13#u16]", "Vec.from [14#u16]")
    refute wrong == source
    File.write!(property, wrong)
    assert_raise RuntimeError, fn -> Project.build!(project, options[:proof_modules]) end

    for extra <- [
          "private axiom uncheckedPrefix : False",
          "private theorem unfinishedPrefix : True := by sorry"
        ] do
      File.write!(property, source <> "\n" <> extra <> "\n")

      error =
        assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

      assert error.message =~ "audit"
    end

    File.write!(property, source)
    rust = Path.join(workspace, "protocol/src/lib.rs")
    original = File.read!(rust)

    broken =
      String.replace(
        original,
        "(values.len() as u64).checked_mul(4)",
        "(values.len() as u64).checked_mul(3)"
      )

    refute broken == original
    File.write!(rust, broken)
    assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end
    File.write!(rust, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
