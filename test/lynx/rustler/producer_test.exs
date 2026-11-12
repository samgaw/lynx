defmodule Lynx.Rustler.ProducerTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for producer NIF roundtrips")

  @tag :tmp_dir
  test "proves arbitrary binary producer roundtrips through compiled Rustler and Elixir", %{
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
        "LynxRustFixture.ProducerNative"
      )
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ProducerNative"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      sysroot: :full_mir,
      cargo: [features: ["producer-protocol"]],
      only: [binary_roundtrip: 1],
      lean_project: project,
      module_prefix: "ProducerNative.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    prepared = Lynx.Rustler.prepare!(options)
    binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "binary_roundtrip"))

    assert %{
             "arity" => 1,
             "flags" => 1,
             "arguments" => ["binary"],
             "result" => %{"option" => "bool"}
           } = binding

    File.write!(
      Path.join(project, "ProducerNative/Properties.lean"),
      File.read!(Path.join(@proofs, "Producer.lean"))
      |> String.replace("__PREFIX__", "ProducerNative")
      |> String.replace("__CORE__", "experiment_nif.experiment_core.nested")
      |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
    )

    File.write!(
      Path.join(project, "ProducerNative/NativeProperties.lean"),
      File.read!(Path.join(@proofs, "ProducerNif.lean"))
      |> String.replace("__FACADE__", binding["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: ["ProducerNative.Properties", "ProducerNative.NativeProperties"],
          required_properties:
            Enum.map(
              ~w(encode_bytes encode_decode binary_roundtrip encode_oversize roundtrip_oversize),
              &("ProducerNative.Properties." <> &1)
            ) ++
              [
                "ProducerNative.NativeProperties.roundtrip",
                "ProducerNative.NativeProperties.oversize"
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
    defmodule LynxRustFixture.ProducerNative do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      #{Enum.join(stubs, "\n")}
    end
    """)

    assert {:ok, [LynxRustFixture.ProducerNative], _} =
             Kernel.ParallelCompiler.compile_to_path([elixir], tmp, return_diagnostics: true)

    native = LynxRustFixture.ProducerNative

    for payload <- [<<>>, <<0, 255, 195, 40>>, :binary.copy(<<169>>, 65535)],
        do: assert(apply(native, :binary_roundtrip, [payload]) == true)

    assert apply(native, :binary_roundtrip, [:binary.copy(<<0>>, 65536)]) == nil
    assert_raise ArgumentError, fn -> apply(native, :binary_roundtrip, [false]) end

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/producer_laws.ex"))
    export = Path.join(tmp, "producer.export")
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

    [{_, false_law}] = Code.compile_file(Path.join(@fixture, "elixir/producer_failures.ex"))
    failed = Lynx.Laws.verify([false_law], native: {Lynx.Rustler, options})

    assert Enum.any?(failed, fn report ->
             report.status == :error and
               Enum.any?(report.diagnostics, &String.contains?(&1.message, "unsolved goals"))
           end)

    core = Path.join(workspace, "core/src/nested.rs")
    original = File.read!(core)
    changed = String.replace(original, "output.push(byte);", "output.push(0);")
    assert changed != original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
