defmodule Lynx.Rust.OrderedCollectionsTest do
  use ExUnit.Case
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @properties Path.expand("../../fixtures/rust_protocol/OrderedCollections.lean", __DIR__)
  @tools System.get_env("LYNX_UNPATCHED_AENEAS_DIR") || System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  unless @tools, do: @moduletag(skip: "set LYNX_AENEAS_DIR for ordered collection proofs")

  @tag :tmp_dir
  test "verifies mutable ordered collections across workspace implementations", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for name <- ~w(Cargo.toml Cargo.lock core analysis nif unrelated),
        do: File.cp_r!(Path.join(@workspace, name), Path.join(workspace, name))

    project = project!(tmp, "proofs", "Tables")
    properties = Path.join(project, "Tables/Properties.lean")
    File.cp!(@properties, properties)

    options = [
      tools: @tools,
      sysroot: :full_mir,
      mir: :promoted,
      lean_project: project,
      module_prefix: "Tables.Extraction",
      build_dir: Path.join(tmp, "build"),
      roots:
        ~w(experiment_analysis::table_replace experiment_analysis::set_insert_twice experiment_analysis::table_stats),
      proof_modules: ["Tables.Properties"],
      required_properties:
        Enum.map(
          ~w(internal_replace internal_claim replace duplicate stats),
          &("Tables.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    assert Enum.all?(result.reports, &(&1.status == :ok))

    assert Enum.all?(
             result.verification.unverified_external_calls,
             &(not &1.implementation_verified)
           )

    assert Enum.any?(
             result.verification.unverified_external_calls,
             &String.contains?(&1.rust_name, "btree")
           )

    assert result.extraction.comparison_projection.omitted != []

    assert Enum.any?(result.extraction.audit.drops.erasures, fn {_, m} ->
             m[:ordered_collection] == "map"
           end)

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok and &1.cached)
           )

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Tables.Properties"])
    export = Path.join(tmp, "ordered.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    independent = project!(tmp, "independent", "Independent")

    File.write!(Path.join(independent, "Independent/Properties.lean"), """
    module
    public import Independent.Extraction.Funs
    public section
    theorem Independent.preserved (value : Aeneas.Std.I64) :
        experiment_unrelated.identity value = .ok value := by rfl
    """)

    independent_opts = [
      tools: @tools,
      lean_project: independent,
      module_prefix: "Independent.Extraction",
      build_dir: Path.join(tmp, "independent-build"),
      roots: ["experiment_unrelated::identity"],
      proof_modules: ["Independent.Properties"],
      required_properties: ["Independent.preserved"]
    ]

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-unrelated", independent_opts).reports,
             &(&1.status == :ok)
           )

    for {relative, before, after_text} <- [
          {"core/src/ordered.rs", "table.insert(key, value)", "table.insert(key, key)"},
          {"core/src/ordered.rs", "values.insert(key)", "values.insert(0)"},
          {"analysis/src/lib.rs", "(previous, table.len() as u64)", "(previous, 0)"}
        ] do
      source = Path.join(workspace, relative)
      original = File.read!(source)
      changed = String.replace(original, before, after_text)
      assert changed != original
      File.write!(source, changed)

      assert_raise RuntimeError, fn ->
        Lynx.Rust.verify!(workspace, "experiment-analysis", options)
      end

      assert Enum.all?(
               Lynx.Rust.verify!(workspace, "experiment-unrelated", independent_opts).reports,
               &(&1.status == :ok and &1.cached)
             )

      File.write!(source, original)
    end

    original = File.read!(properties)

    File.write!(
      properties,
      String.replace(original, ".ok (some value)", ".ok (some replacement)")
    )

    assert_raise RuntimeError, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(properties, original)

    model = Path.join(project, "Tables/Extraction/OrderedCollectionsModel.lean")
    model_source = File.read!(model)
    File.write!(model, String.replace(model_source, "else .fail .undef", "else .fail .panic"))
    assert_raise RuntimeError, fn -> Lynx.Rust.Project.build!(project, ["Tables.Properties"]) end
    File.write!(model, model_source)
    Lynx.Rust.Project.build!(project, ["Tables.Properties"])

    for extra <- [
          "private axiom unapproved_tree : False",
          "private theorem unfinished_tree : True := by sorry"
        ] do
      File.write!(model, model_source <> "\n" <> extra <> "\n")
      Lynx.Rust.Project.build!(project, ["Tables.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
      File.write!(model, model_source)
      Lynx.Rust.Project.build!(project, ["Tables.Properties"])
    end

    source = Path.join(workspace, "core/src/ordered.rs")
    rust = File.read!(source)

    File.write!(
      source,
      String.replace(
        rust,
        "table.insert(key, value)",
        "let previous = table.remove(&key); table.insert(key, value); previous"
      )
    )

    assert_raise CompileError, ~r/unverified external Rust call.*remove/, fn ->
      Lynx.Rust.verify!(workspace, "experiment-analysis", options)
    end

    File.write!(source, rust)

    assert Enum.all?(
             Lynx.Rust.verify!(workspace, "experiment-analysis", options).reports,
             &(&1.status == :ok)
           )
  end

  defp project!(tmp, directory, name) do
    project = Path.join(tmp, directory)
    File.mkdir_p!(Path.join(project, name))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.join(@workspace, "proofs/.lake/packages"),
      Path.join(project, ".lake/packages")
    )

    project
  end
end
