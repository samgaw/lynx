defmodule Lynx.Rustler.ConsumeTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for consuming NIF proofs")

  @tag :tmp_dir
  test "proves exact consumption and comparator order through compiled NIF laws", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      File.read!(source)
      |> String.replace("LynxRustFixture.BinaryNative", "LynxRustFixture.ConsumeNative")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Consume"))
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
      cargo: [features: ["prefix-consume"]],
      only: [payload_length: 1, checked_consume: 0, checked_recognize: 0],
      lean_project: project,
      module_prefix: "Consume.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)
    bindings = Map.new(discovered.bindings.bindings, &{&1["name"], &1})

    assert %{
             "arity" => 1,
             "flags" => 1,
             "arguments" => ["binary"],
             "result" => %{"option" => "u64"}
           } = bindings["payload_length"]

    for name <- ~w(checked_consume checked_recognize),
        do:
          assert(
            %{"arity" => 0, "flags" => 0, "arguments" => [], "result" => "bool"} = bindings[name]
          )

    File.write!(
      Path.join(project, "Consume/Properties.lean"),
      File.read!(Path.join(@proofs, "Consume.lean"))
      |> String.replace("__ROOT__", "experiment_nif")
      |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
      |> String.replace("__CORE__", "experiment_nif.experiment_core.protocol")
    )

    File.write!(
      Path.join(project, "Consume/NativeProperties.lean"),
      File.read!(Path.join(@proofs, "ConsumeNif.lean"))
      |> String.replace("__PAYLOAD__", bindings["payload_length"]["lean_name"])
      |> String.replace("__CHECKED__", bindings["checked_consume"]["lean_name"])
      |> String.replace("__RECOGNIZE__", bindings["checked_recognize"]["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: ["Consume.Properties", "Consume.NativeProperties"],
          required_properties:
            Enum.map(
              ~w(consume_bytes conservation marker_bytes length_bytes empty_prefix comparator_panic recognize_without_panic),
              &("Consume.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(facade_bytes payload exact_marker mismatch truncated comparator_panic recognition_order),
                &("Consume.NativeProperties." <> &1)
              )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))
    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    [{module, _}] =
      Code.compile_string("""
      defmodule LynxRustFixture.ConsumeNative do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    assert apply(module, :payload_length, [<<"LYNX", 0, 255>>]) == 2
    assert apply(module, :payload_length, ["LYNX"]) == 0
    for bad <- ["LYNY", "LYN", <<>>], do: assert(apply(module, :payload_length, [bad]) == nil)
    assert catch_error(apply(module, :checked_consume, [])) == :nif_panicked
    refute apply(module, :checked_recognize, [])
    assert catch_error(apply(module, :payload_length, [false])) == :badarg
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/consume_laws.ex"))
    export = Path.join(tmp, "consume.export")
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
    [{_, false_law}] = Code.compile_file(Path.join(@fixture, "elixir/consume_failures.ex"))
    failed = Lynx.Laws.verify([false_law], native: {Lynx.Rustler, options})
    assert Enum.any?(failed, &(&1.status == :error))

    assert Enum.any?(failed, fn report ->
             Enum.any?(report.diagnostics, &(&1.message =~ "unsolved goals"))
           end)

    core = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(core)

    changed =
      String.replace(
        original,
        "input.strip_prefix(prefix)",
        "match input.strip_prefix(prefix) { Some(_) => Some(input), None => None }"
      )

    assert changed != original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
