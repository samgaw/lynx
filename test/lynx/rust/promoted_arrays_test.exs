defmodule Lynx.Rust.PromotedArraysTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/PromotedArrays.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for promoted array proofs")

  @tag :tmp_dir
  test "proves actual immutable promoted array contents across crates", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "PromotedArrays"))
    File.cp!(@proof, Path.join(project, "PromotedArrays/Properties.lean"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      roots: ["experiment_analysis::default_bytes", "experiment_analysis::magic_bytes"],
      lean_project: project,
      module_prefix: "PromotedArrays.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["PromotedArrays.Properties"],
      required_properties:
        Enum.map(~w(core_empty core_magic empty magic), &("PromotedArrays.Properties." <> &1))
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports
    assert Enum.count(result.verification.constants, &(&1["status"] == :inlined)) == 2

    assert [
             %{
               rust_name: "core::array::{[@T; @N]}::as_slice",
               implementation_verified: false,
               status: :modelled
             }
           ] =
             result.verification.unverified_external_calls

    assert Enum.any?(result.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    export = Path.join(tmp, "arrays.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["PromotedArrays.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    for {before, after_change} <- [{"&[]", "&[0]"}, {"&[76, 89, 78, 88]", "&[76, 89, 78, 89]"}] do
      changed = String.replace(original, before, after_change)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
  end
end
