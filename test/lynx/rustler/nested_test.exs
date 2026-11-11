defmodule Lynx.Rustler.NestedTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for nested parser NIF proofs")

  @tag :tmp_dir
  test "proves actual recursive parser behavior through compiled Rustler and Elixir", %{
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
        "LynxRustFixture.BinaryNative",
        "LynxRustFixture.NestedNative"
      )
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "NestedNative"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      cargo: [features: ["nested-protocol"]],
      only: [document_nodes: 3],
      lean_project: project,
      module_prefix: "NestedNative.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)
    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "document_nodes"))

    assert %{
             "arity" => 3,
             "flags" => 1,
             "arguments" => ["binary", "u8", "u16"],
             "result" => %{"option" => "u16"}
           } = binding

    for {file, target} <- [{"Nested.lean", "Properties"}, {"NestedCases.lean", "Cases"}] do
      File.write!(
        Path.join(project, "NestedNative/#{target}.lean"),
        File.read!(Path.join(@proofs, file))
        |> String.replace("__PREFIX__", "NestedNative")
        |> String.replace("__CORE__", "experiment_nif.experiment_core.nested")
        |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
      )
    end

    File.write!(
      Path.join(project, "NestedNative/NativeProperties.lean"),
      File.read!(Path.join(@proofs, "NestedNif.lean"))
      |> String.replace("__FACADE__", binding["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: [
            "NestedNative.Properties",
            "NestedNative.Cases",
            "NestedNative.NativeProperties"
          ],
          required_properties: [
            "NestedNative.Properties.scan_total",
            "NestedNative.Properties.document_total",
            "NestedNative.Cases.siblings",
            "NestedNative.Cases.document_siblings",
            "NestedNative.NativeProperties.facade_bounded",
            "NestedNative.NativeProperties.facade_siblings"
          ]
        ]

    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    elixir = Path.join(tmp, "native.ex")

    File.write!(elixir, """
    defmodule LynxRustFixture.NestedNative do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxRustFixture.NestedNative], _} =
             Kernel.ParallelCompiler.compile_to_path([elixir], tmp, return_diagnostics: true)

    native = LynxRustFixture.NestedNative
    packet = <<1, 0, 8, 0, 0, 0, 2, 0, 2, 195, 169>>
    assert apply(native, :document_nodes, [packet, 2, 3]) == 3
    assert apply(native, :document_nodes, [packet, 1, 3]) == nil
    assert apply(native, :document_nodes, [packet, 2, 2]) == nil

    assert apply(native, :document_nodes, [packet, 258, 65539]) == 3

    for args <- [[packet, 4_294_967_296, 3], [packet, 2, 4_294_967_296], [false, 2, 3]],
        do: assert_raise(ArgumentError, fn -> apply(native, :document_nodes, args) end)

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/nested_laws.ex"))
    export = Path.join(tmp, "nested.export")
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

    [{_, false_law}] = Code.compile_file(Path.join(@fixture, "elixir/nested_failures.ex"))
    failed = Lynx.Laws.verify([false_law], native: {Lynx.Rustler, options})

    assert Enum.any?(failed, fn report ->
             report.status == :error and
               Enum.any?(report.diagnostics, &String.contains?(&1.message, "unsolved goals"))
           end)

    core = Path.join(workspace, "core/src/nested.rs")
    original = File.read!(core)
    changed = String.replace(original, "used += child.nodes;", "used += 0;")
    assert changed != original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
