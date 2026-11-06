defmodule Lynx.Rust.StaticBorrowTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../fixtures/rust_static_borrow", __DIR__)
  @packages Path.expand("../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools),
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned patched Aeneas distribution")

  @tag tmp_dir: "process-#{System.pid()}"
  test "preserves static strings borrowed through an enum and generic helper", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.cp_r!(@fixture, workspace)
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Nested"))

    File.cp!(
      Path.join(workspace, "Properties.lean"),
      Path.join(project, "Nested/Properties.lean")
    )

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["nested_static::nested", "nested_static::extract"],
      lean_project: project,
      module_prefix: "Nested.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Nested.Properties"],
      required_properties: [
        "Nested.preserves_string",
        "Nested.empty_result",
        "Nested.detects_text"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "nested-static", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.unverified_external_calls == []
    assert map_size(result.extraction.implementations) == 3

    assert result.extraction.translation["aeneas_version"] in [
             "nightly-2026.11.04-2b9e3ea+lynx-static-loans-v1",
             "nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1",
             "nightly-2026.11.04-2b9e3ea+lynx-result-monad-v1+assertion-unwind-v1"
           ]

    export = Path.join(tmp, "static-borrow.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["Nested.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "src/lib.rs")

    File.write!(
      source,
      String.replace(File.read!(source), "Some(*shared(&text))", "Some(\"changed\")")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "nested-static", options)
    end
  end
end
