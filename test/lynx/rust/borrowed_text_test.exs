defmodule Lynx.Rust.BorrowedTextTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @properties Path.expand("../../fixtures/rust_protocol/BorrowedTextProperties.lean", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for borrowed text proofs")

  @tag :tmp_dir
  test "proves shared text and byte-oriented headers independently of Rustler", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, name), Path.join(workspace, name))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "BorrowedText"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    path = Path.join(project, "BorrowedText/Properties.lean")

    properties =
      File.read!(@properties)
      |> String.replace("__CALLER__", "experiment_analysis")
      |> String.replace("__CORE__", "experiment_analysis.experiment_core.protocol")

    File.write!(path, properties)

    required =
      Enum.map(
        ~w(borrowed_echo borrowed_header_composition borrowed_header_short borrowed_header_value borrowed_network_order),
        &("BorrowedText.Properties." <> &1)
      )

    options = [
      tools: @tools,
      lean_project: project,
      module_prefix: "BorrowedText.Extraction",
      roots: ["experiment_analysis::borrowed_text", "experiment_analysis::borrowed_text_header"],
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["BorrowedText.Properties"],
      required_properties: required
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert Enum.all?(result.reports, &(&1.status == :ok))

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok and &1.cached)
           )

    file = Lynx.Rust.Proofs.file!(result.extraction, ["BorrowedText.Properties"])
    export = Path.join(tmp, "borrowed-text.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for {path, before, after_text} <- [
          {path, "1280921176#u32", "1#u32"},
          {Path.join(workspace, "core/src/protocol.rs"),
           "pub fn borrowed_text(text: &str) -> &str {\n    text\n}",
           "pub fn borrowed_text(text: &str) -> &str {\n    \"\"\n}"},
          {Path.join(workspace, "analysis/src/lib.rs"),
           "experiment_core::protocol::read_header(experiment_core::protocol::text_bytes(text))",
           "None"}
        ] do
      original = File.read!(path)
      changed = String.replace(original, before, after_text)
      refute changed == original
      File.write!(path, changed)

      assert_raise RuntimeError, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      File.write!(path, original)
    end

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok)
           )
  end
end
