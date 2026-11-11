defmodule Lynx.Rust.NestedTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Nested.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for recursive parser proofs")

  @tag :tmp_dir
  test "proves recursive parser totality and budgets across actual crate bodies", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Nested"))

    for {source, target} <- [
          {@proof, "Properties"},
          {String.replace(@proof, "Nested.lean", "NestedCases.lean"), "Cases"}
        ] do
      File.write!(
        Path.join(project, "Nested/#{target}.lean"),
        File.read!(source)
        |> String.replace("__PREFIX__", "Nested")
        |> String.replace("__CORE__", "experiment_analysis.experiment_core.nested")
        |> String.replace("__ANALYSIS__", "experiment_analysis")
      )
    end

    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      tools: @tools,
      roots: ["experiment_analysis::document_nodes"],
      lean_project: project,
      module_prefix: "Nested.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Nested.Properties", "Nested.Cases"],
      required_properties: [
        "Nested.Properties.scan_total",
        "Nested.Properties.document_total",
        "Nested.Cases.siblings",
        "Nested.Cases.document_siblings",
        "Nested.Cases.too_shallow"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract and
               guarantee.theorem == "Nested.Properties.document_total" and
               "Nested.Properties.scan_total" in guarantee.contracts_used
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    File.write!(unrelated, File.read!(unrelated) <> "\n// Independent revision.\n")

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Nested.Properties", "Nested.Cases"])
    export = Path.join(tmp, "nested.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    loop_path = Path.join(project, "Nested/NativeLoops.lean")
    original_loop = File.read!(loop_path)

    for declaration <- [
          "private axiom unexpected : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(loop_path, original_loop <> "\n" <> declaration <> "\n")
      Lynx.Rust.Project.build!(project, ["Nested.Properties", "Nested.Cases"])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(loop_path, original_loop)

    source = Path.join(workspace, "core/src/nested.rs")
    original = File.read!(source)
    changed = String.replace(original, "consumed: total", "consumed: 0")
    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
  end
end
