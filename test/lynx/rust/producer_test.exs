defmodule Lynx.Rust.ProducerTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Producer.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for producer roundtrips")

  @tag :tmp_dir
  test "proves actual producer bytes and borrowed decoder roundtrips across crates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Producer"))

    File.write!(
      Path.join(project, "Producer/Properties.lean"),
      File.read!(@proof)
      |> String.replace("__PREFIX__", "Producer")
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.nested")
      |> String.replace("__ANALYSIS__", "experiment_analysis")
    )

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      sysroot: :full_mir,
      roots: ["experiment_analysis::binary_roundtrip"],
      lean_project: project,
      module_prefix: "Producer.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Producer.Properties"],
      required_properties:
        Enum.map(
          ~w(encode_bytes encode_decode binary_roundtrip encode_oversize roundtrip_oversize),
          &("Producer.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract and
               guarantee.theorem == "Producer.Properties.binary_roundtrip" and
               "Producer.Properties.encode_decode" in guarantee.contracts_used
           end)

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.label, "shared-slice iterator")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    File.write!(unrelated, File.read!(unrelated) <> "\n// Independent revision.\n")

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Producer.Properties"])
    export = Path.join(tmp, "producer.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    source = Path.join(workspace, "core/src/nested.rs")
    original = File.read!(source)

    for {before, after_text} <- [
          {"output.push(byte);", "output.push(0);"},
          {".to_be_bytes();", ".to_le_bytes();"}
        ] do
      changed = String.replace(original, before, after_text)
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
