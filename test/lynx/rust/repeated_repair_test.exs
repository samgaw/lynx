defmodule Lynx.Rust.RepeatedRepairTest do
  use ExUnit.Case
  alias Lynx.Rust.{Project, Proofs}
  Code.require_file("../../support/rust_io.exs", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools && File.regular?(Path.join(@tools, "lynx-toolchain")),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned native backend")

  @tag :tmp_dir
  test "repeated actual Rust repair preserves arbitrary bounded logs", %{tmp_dir: tmp} do
    {workspace, project, base} =
      Lynx.Rust.IoFixture.prepare!(tmp, @tools, ["RepeatedRepairProperties"])

    options =
      base
      |> Keyword.put(:proof_modules, ["Record.RepeatedRepairProperties"])
      |> Keyword.put(
        :required_properties,
        Enum.map(
          ~w(clean_repair repair_idempotent repair_repeated),
          &("Record.RepeatedRepairProperties." <> &1)
        )
      )

    result = Lynx.Rust.verify!(workspace, "io-protocol", options)
    assert [%{status: :ok}] = result.reports

    for theorem <- ~w(clean_repair repair_idempotent repair_repeated) do
      assert Enum.any?(result.verification.guarantees, fn evidence ->
               evidence.kind == :cross_crate_contract &&
                 evidence.theorem == "Record.RepeatedRepairProperties." <> theorem
             end)
    end

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "io-protocol", options).reports

    file =
      Proofs.file!(result.extraction, options[:proof_modules],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "repeated-repair.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    property = Path.join(project, "Record/RepeatedRepairProperties.lean")
    source = File.read!(property)

    wrong =
      String.replace(source, "alloc.vec.Vec.from values", "alloc.vec.Vec.from values.reverse")

    refute wrong == source
    File.write!(property, wrong)
    error = assert_raise RuntimeError, fn -> Project.build!(project, options[:proof_modules]) end
    assert error.message =~ "RepeatedRepairProperties.lean:"
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

    error =
      assert_raise RuntimeError, fn -> Lynx.Rust.verify!(workspace, "io-protocol", options) end

    assert error.message =~ ".lean:"
    File.write!(rust, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "io-protocol", options).reports
  end
end
