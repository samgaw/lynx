defmodule Lynx.Rustler.PrefixTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proofs Path.expand("../../fixtures/rust_protocol", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools) or System.get_env("LYNX_FULL_MIR") != "1",
    do: @moduletag(skip: "set LYNX_AENEAS_DIR and LYNX_FULL_MIR=1 for compiled prefix laws")

  @tag :tmp_dir
  test "proves compiled NIF prefix laws and comparator panic conversion", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@fixture, entry), Path.join(workspace, entry))

    source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      source,
      File.read!(source)
      |> String.replace("LynxRustFixture.BinaryNative", "LynxRustFixture.PrefixNative")
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Prefix"))
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
      cargo: [features: ["slice-prefix"]],
      only: [wire_prefix: 1, checked_prefix: 1],
      lean_project: project,
      module_prefix: "Prefix.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)
    bindings = Map.new(discovered.bindings.bindings, &{&1["name"], &1})

    assert %{"arity" => 1, "flags" => 1, "arguments" => ["binary"], "result" => "bool"} =
             bindings["wire_prefix"]

    assert %{"arity" => 1, "flags" => 0, "arguments" => ["bool"], "result" => "bool"} =
             bindings["checked_prefix"]

    File.write!(
      Path.join(project, "Prefix/Properties.lean"),
      File.read!(Path.join(@proofs, "Prefix.lean"))
      |> String.replace("__CORE__", "experiment_nif.experiment_core.protocol")
      |> String.replace("__ANALYSIS__", "experiment_nif.experiment_analysis")
      |> String.replace("__HELPER__", "experiment_nif.core.slice.Slice.starts_with")
    )

    File.write!(
      Path.join(project, "Prefix/NativeProperties.lean"),
      File.read!(Path.join(@proofs, "PrefixNif.lean"))
      |> String.replace("__RECOGNIZE__", bindings["wire_prefix"]["lean_name"])
      |> String.replace("__CHECKED__", bindings["checked_prefix"]["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: ["Prefix.Properties", "Prefix.NativeProperties"],
          required_properties:
            Enum.map(
              ~w(prefix_bytes marker_exact marker_payload reject_short empty_prefix composition short_circuit comparator_panic),
              &("Prefix.Properties." <> &1)
            ) ++
              Enum.map(
                ~w(marker_exact marker_payload reject_short short_circuit comparator_panic),
                &("Prefix.NativeProperties." <> &1)
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
      defmodule LynxRustFixture.PrefixNative do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    assert apply(module, :wire_prefix, ["LYNX"])
    assert apply(module, :wire_prefix, [<<"LYNX", 0, 255, 128>>])
    refute apply(module, :wire_prefix, [<<>>])
    refute apply(module, :wire_prefix, ["LYNY"])
    refute apply(module, :checked_prefix, [false])
    assert catch_error(apply(module, :checked_prefix, [true])) == :nif_panicked
    assert catch_error(apply(module, :wire_prefix, [false])) == :badarg
    [{_, beam}] = Code.compile_file(Path.join(@fixture, "elixir/prefix_laws.ex"))
    export = Path.join(tmp, "prefix.export")
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
    [{_, false_law}] = Code.compile_file(Path.join(@fixture, "elixir/prefix_failures.ex"))

    failed = Lynx.Laws.verify([false_law], native: {Lynx.Rustler, options})
    assert Enum.any?(failed, &(&1.status == :error))

    assert Enum.any?(failed, fn report ->
             Enum.any?(report.diagnostics, &(&1.message =~ "unsolved goals"))
           end)

    core = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(core)
    changed = String.replace(original, "input.starts_with(prefix)", "!input.starts_with(prefix)")
    assert changed != original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(core, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
