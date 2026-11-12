defmodule Lynx.Rust.TreeTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/Tree.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for recursive tree proofs")

  @tag :tmp_dir
  test "proves recursive tree construction, exact counts and budget rejection across crates", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Tree"))

    for {source, target} <- [
          {"TreeCore.lean", "CoreProperties"},
          {"TreeDriver.lean", "DriverProperties"},
          {"Tree.lean", "Properties"}
        ] do
      File.write!(
        Path.join(project, "Tree/#{target}.lean"),
        File.read!(Path.join(Path.dirname(@proof), source))
        |> String.replace("__PREFIX__", "Tree")
        |> String.replace("__CORE__", "experiment_analysis.experiment_core.tree")
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
      roots: ["experiment_analysis::tree_nodes", "experiment_analysis::binary_tree_nodes"],
      lean_project: project,
      module_prefix: "Tree.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["Tree.CoreProperties", "Tree.DriverProperties", "Tree.Properties"],
      required_properties:
        Enum.map(
          ~w(count_exact count_total inspect_exact inspect_fits inspect_rejects append_exact singleton_payload binary_tree_payload constructed_count count_owned_exact binary_tree_nodes),
          &("Tree.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert [%{status: :ok}] = result.reports

    drops = result.verification.structural_drops
    assert Enum.any?(drops, &(&1.type == "alloc::vec::Vec<u8>"))
    assert Enum.any?(drops, &(&1.type == "alloc::vec::Vec<experiment_core::tree::Node>"))

    assert Enum.any?(drops, fn drop ->
             drop.type == "experiment_core::tree::Node" and
               drop.status == :audited_erasure and not drop.implementation_verified
           end)

    assert Enum.any?(
             result.extraction.native_unwind,
             &(&1.kind == :nonpanicking_collection_call and &1.method == "push")
           )

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract and
               guarantee.theorem == "Tree.Properties.inspect_exact" and
               "Tree.Properties.count_exact" in guarantee.contracts_used
           end)

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    unrelated = Path.join(workspace, "unrelated/src/lib.rs")
    File.write!(unrelated, File.read!(unrelated) <> "\n// Independent revision.\n")

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    file = Lynx.Rust.Proofs.file!(result.extraction, options[:proof_modules])
    export = Path.join(tmp, "tree.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    source = Path.join(workspace, "core/src/tree.rs")
    original = File.read!(source)

    changed =
      String.replace(
        original,
        "used += count(child, budget - used)?;",
        "used += count(child, budget - used)? - 1;"
      )

    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    caller = Path.join(workspace, "analysis/src/lib.rs")
    original_caller = File.read!(caller)

    changed_caller =
      String.replace(
        original_caller,
        "experiment_core::tree::count(node, budget)",
        "experiment_core::tree::count(node, 0)"
      )

    assert changed_caller != original_caller
    File.write!(caller, changed_caller)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(caller, original_caller)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    corrupted =
      String.replace(
        original,
        "children.push(child);",
        "children.push(child);\n    children.push(Node::Sequence(Vec::new()));"
      )

    assert corrupted != original
    File.write!(source, corrupted)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    reachable_drop =
      String.replace(
        original,
        "children.push(child);",
        "let _discarded = Node::Sequence(Vec::new());\n    children.push(child);"
      )

    assert reachable_drop != original
    File.write!(source, reachable_drop)

    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports

    File.write!(
      source,
      original <> "\nimpl Drop for Node { fn drop(&mut self) { panic!(\"observable drop\"); } }\n"
    )

    assert_raise CompileError,
                 ~r/observable or unsupported behavior in compiler-generated drop glue/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "experiment-analysis", options)
                 end

    File.write!(source, original)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports
  end
end
