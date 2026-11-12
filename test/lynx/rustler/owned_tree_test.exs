defmodule Lynx.Rustler.OwnedTreeTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for owned tree NIF proofs")

  @tag :tmp_dir
  test "proves construction traversal and structural cleanup through a compiled Rustler NIF", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      String.replace(
        File.read!(source),
        "LynxRustFixture.Native",
        "LynxRustFixture.OwnedTreeNative"
      )
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "OwnedTreeNative"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      cargo: [features: ["owned-tree"]],
      only: [owned_tree_nodes: 2],
      lean_project: project,
      module_prefix: "OwnedTreeNative.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)
    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "owned_tree_nodes"))

    assert %{
             "arity" => 2,
             "flags" => 1,
             "arguments" => [%{"vec" => "u8"}, "u16"],
             "result" => %{"option" => "u16"}
           } = binding

    for {source, target} <- [
          {"TreeCore.lean", "CoreProperties"},
          {"TreeDriver.lean", "DriverProperties"},
          {"TreeNif.lean", "NativeProperties"}
        ] do
      File.write!(
        Path.join(project, "OwnedTreeNative/#{target}.lean"),
        File.read!(Path.join(@proofs, source))
        |> String.replace("__PREFIX__", "OwnedTreeNative")
        |> String.replace("__CORE__", "experiment_nif.experiment_core.tree")
        |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
        |> String.replace("__FACADE__", binding["lean_name"])
      )
    end

    options =
      options ++
        [
          proof_modules: [
            "OwnedTreeNative.CoreProperties",
            "OwnedTreeNative.DriverProperties",
            "OwnedTreeNative.NativeProperties"
          ],
          required_properties:
            Enum.map(
              ~w(count_exact count_owned_exact append_exact singleton_payload binary_tree_payload binary_tree_nodes),
              &("OwnedTreeNative.Properties." <> &1)
            ) ++ ["OwnedTreeNative.NativeProperties.facade"]
        ]

    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    elixir = Path.join(tmp, "native.ex")

    File.write!(elixir, """
    defmodule LynxRustFixture.OwnedTreeNative do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxRustFixture.OwnedTreeNative], _} =
             Kernel.ParallelCompiler.compile_to_path([elixir], tmp, return_diagnostics: true)

    native = LynxRustFixture.OwnedTreeNative

    for payload <- [[], [0, 255, 195, 40], Enum.to_list(0..255)] do
      assert apply(native, :owned_tree_nodes, [payload, 2]) == 2
      assert apply(native, :owned_tree_nodes, [payload, 1]) == nil
      assert apply(native, :owned_tree_nodes, [payload, 0]) == nil
    end

    assert apply(native, :owned_tree_nodes, [[256, 4_294_967_295], 65538]) == 2
    assert catch_error(apply(native, :owned_tree_nodes, [[0 | 1], 2])) == :nif_panicked

    for {payload, budget} <- [{false, 2}, {[-1], 2}, {[false], 2}, {[], 4_294_967_296}],
        do:
          assert_raise(ArgumentError, fn ->
            apply(native, :owned_tree_nodes, [payload, budget])
          end)

    laws_source = File.read!(Path.join(@fixture, "elixir/owned_tree_laws.ex"))
    [{_, beam}] = Code.compile_string(laws_source)
    export = Path.join(tmp, "owned-tree.export")
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    false_source =
      laws_source
      |> String.replace("OwnedTreeLaws", "OwnedTreeFalseLaws")
      |> String.replace("owned_tree_nodes(input, 2) == 2", "owned_tree_nodes(input, 2) == 3")

    assert false_source != String.replace(laws_source, "OwnedTreeLaws", "OwnedTreeFalseLaws")
    [{_, false_beam}] = Code.compile_string(false_source)

    assert Enum.any?(Lynx.Laws.verify([false_beam], native: {Lynx.Rustler, options}), fn report ->
             report.status == :error and
               Enum.any?(report.diagnostics, &String.contains?(&1.message, "unsolved goals"))
           end)

    core = Path.join(project, "OwnedTreeNative/CoreProperties.lean")
    original_core = File.read!(core)
    file = Lynx.Rust.Proofs.file!(prepared.extraction, options[:proof_modules])

    for declaration <- [
          "private axiom unexpected : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(core, original_core <> "\n" <> declaration <> "\n")
      Lynx.Rust.Project.build!(project, options[:proof_modules])

      assert [%{status: :error, diagnostics: diagnostics}] =
               Lynx.Commands.verify!(project, [file])

      assert Enum.any?(diagnostics, &String.contains?(&1.message, "unexpected axiom"))
    end

    File.write!(core, original_core)
    rust = Path.join(workspace, "core/src/tree.rs")
    original = File.read!(rust)

    changed =
      String.replace(
        original,
        "used += count(child, budget - used)?;",
        "used += count(child, budget - used)? - 1;"
      )

    assert changed != original
    File.write!(rust, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(rust, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
