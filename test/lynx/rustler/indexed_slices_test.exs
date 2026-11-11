defmodule Lynx.Rustler.IndexedSlicesTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for indexed NIF proofs")

  @tag :tmp_dir
  test "preserves indexed bytes, bounds panics and decoding through Rustler laws", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      File.read!(source)
      |> String.replace("LynxRustFixture.BinaryNative", "LynxRustFixture.IndexedNative")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Indexed"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      cargo: [features: ["slice-index"]],
      only: [window_length: 3],
      lean_project: project,
      module_prefix: "Indexed.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)

    assert [
             %{
               "name" => "window_length",
               "arity" => 3,
               "flags" => 1,
               "arguments" => ["binary", "u8", "u8"],
               "result" => "u64"
             } = binding
           ] = discovered.bindings.bindings

    File.write!(
      Path.join(project, "Indexed/WindowProperties.lean"),
      File.read!(Path.join(@proofs, "IndexedWindow.lean"))
      |> String.replace("__CORE__", "experiment_nif.experiment_core")
      |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
    )

    File.write!(
      Path.join(project, "Indexed/NativeProperties.lean"),
      File.read!(Path.join(@proofs, "IndexedNif.lean"))
      |> String.replace("__FACADE__", binding["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: ["Indexed.WindowProperties", "Indexed.NativeProperties"],
          required_properties:
            Enum.map(
              ~w(core_window window_bytes),
              &("Indexed.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(facade success reversed truncated),
                &("Indexed.NativeProperties." <> &1)
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
      defmodule LynxRustFixture.IndexedNative do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    assert apply(module, :window_length, [<<0, 255, 128>>, 1, 3]) == 2
    assert catch_error(apply(module, :window_length, [<<0, 255, 128>>, 3, 1])) == :nif_panicked
    assert catch_error(apply(module, :window_length, [<<0, 255, 128>>, 0, 4])) == :nif_panicked
    assert apply(module, :window_length, [<<0, 255, 128>>, 0, 256]) == 0

    assert catch_error(apply(module, :window_length, [<<0, 255, 128>>, 0, 4_294_967_296])) ==
             :badarg

    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/indexed_laws.ex"))
    export = Path.join(tmp, "indexed.export")
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
    [{_, false_law}] = Code.compile_file(Path.join(@fixture, "elixir/indexed_failures.ex"))
    failed = Lynx.Laws.verify([false_law], native: {Lynx.Rustler, options})
    assert Enum.any?(failed, &(&1.status == :error))

    assert Enum.any?(failed, fn report ->
             Enum.any?(report.diagnostics, &(&1.message =~ "unsolved goals"))
           end)

    core = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(core)
    changed = String.replace(original, "&input[start..end]", "&input[..end]")
    assert changed != original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
