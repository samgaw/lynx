defmodule Lynx.Rustler.NamedArrayTest do
  use ExUnit.Case
  @tools System.get_env("LYNX_AENEAS_DIR")
  @workspace Path.expand("../../fixtures/rust_workspace", __DIR__)
  @proof Path.expand("../../fixtures/rust_protocol/NamedArrayNif.lean", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for named array NIF proofs")

  @tag :tmp_dir
  test "links named array initializers through Rustler and an Elixir law", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for entry <- ~w(Cargo.toml Cargo.lock core analysis unrelated nif),
        do: File.cp_r!(Path.join(@workspace, entry), Path.join(workspace, entry))

    native_source = Path.join(workspace, "nif/src/lib.rs")

    File.write!(
      native_source,
      String.replace(
        File.read!(native_source),
        "LynxRustFixture.Native",
        "LynxRustFixture.NamedArrayNative"
      )
    )

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "NamedArrayNif"))
    packages = Path.join(@workspace, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "experiment-nif",
      tools: @tools,
      cargo: [features: ["named-arrays"]],
      only: [wire_marker: 0],
      lean_project: project,
      module_prefix: "NamedArrayNif.Extraction",
      build_dir: Path.join(tmp, "build")
    ]

    discovered = Lynx.Rustler.prepare!(options)

    assert [%{"name" => "wire_marker", "arity" => 0, "flags" => 0, "result" => "u32"} = binding] =
             discovered.bindings.bindings

    File.write!(
      Path.join(project, "NamedArrayNif/Properties.lean"),
      String.replace(File.read!(@proof), "__FACADE__", binding["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: ["NamedArrayNif.Properties"],
          required_properties:
            Enum.map(~w(core_spec composition facade), &("NamedArrayNif.Properties." <> &1))
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(prepared.reports, &(&1.status == :ok))

    assert Enum.any?(
             prepared.verification.constants,
             &(&1["status"] == :extracted and String.ends_with?(&1["lean_name"], ".WIRE_MAGIC"))
           )

    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")

    stubs =
      for {name, arity, _} <- prepared.bindings.exports,
          do:
            "def #{name}(#{Enum.join(List.duplicate("_", arity), ",")}), do: :erlang.nif_error(:not_loaded)"

    [{module, _}] =
      Code.compile_string("""
      defmodule LynxRustFixture.NamedArrayNative do
        @compile :debug_info
        @on_load :load_nif
        def load_nif, do: :erlang.load_nif(~c"#{library}",0)
        #{Enum.join(stubs, "\n")}
      end
      """)

    assert apply(module, :wire_marker, []) == 1_280_921_176
    [{_, beam}] = Code.compile_file(Path.join(@workspace, "elixir/named_array_laws.ex"))
    export = Path.join(tmp, "named-array.export")
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

    source = Path.join(workspace, "core/src/protocol.rs")
    original = File.read!(source)

    changed =
      String.replace(
        original,
        "WIRE_MAGIC: [u8; 4] = [76, 89, 78, 88]",
        "WIRE_MAGIC: [u8; 4] = [76, 89, 78, 89]"
      )

    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
