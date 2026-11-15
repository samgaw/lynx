defmodule Lynx.Rustler.EnumStateTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_ENUM_DIR")
  @moduletag timeout: 1_800_000
  unless @tools, do: @moduletag(skip: "set LYNX_NATIVE_ENUM_DIR for enum native state proofs")

  @tag :tmp_dir
  test "composes nested enum receive transitions across a real mutex and compiled NIF", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")
    File.write!(rust, String.replace(File.read!(rust), "LynxAtomicFixture", "LynxPhaseFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Phase"))
    File.mkdir_p!(Path.join(project, ".lake"))

    File.ln_s!(
      Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__),
      Path.join(project, ".lake/packages")
    )

    common = [
      workspace: workspace,
      package: "atomic-nif",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      branching: :duplicate,
      root_attribute: "lynx::phase",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Phase.Extraction",
      only: [consume_chunks: 3]
    ]

    prepared = Lynx.Rustler.prepare!(common)
    [binding] = prepared.bindings.bindings

    properties =
      File.read!(Path.join(@fixture, "PhaseProperties.lean"))
      |> String.replace("__NIF__", binding["lean_name"])

    property = Path.join(project, "Phase/Properties.lean")
    File.write!(property, properties)

    options =
      common ++
        [
          proof_modules: ["Phase.Properties"],
          required_properties:
            Enum.map(
              ~w(start_contract terminal_stable completion_total receiving_bounded locked_contract facade_contract facade_run),
              &("Phase.Properties." <> &1)
            )
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))

    for name <- ~w(Phase Completion CompletionKind) do
      type =
        Enum.find(prepared.extraction.audit.translated["type_decls"], fn type ->
          type &&
            type["item_meta"]["name"] == [
              %{"Ident" => ["atomic_core", 0]},
              %{"Ident" => [name, 0]}
            ]
        end)

      assert %{"needs_drop" => false} = type

      assert %{type_id: type["def_id"], needs_drop: false} in prepared.verification.compiler_drop_queries
    end

    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxPhaseFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxPhaseFixture.Native

    for {args, expected} <- [
          {[10, 3, 4], {true, true, 7}},
          {[10, 6, 4], {true, true, 10}},
          {[10, 10, 1], {true, false, 10}},
          {[10, 11, 0], {false, false, 0}},
          {[18_446_744_073_709_551_615, 18_446_744_073_709_551_614, 2], {true, false, 0}},
          {[0, 0, 0], {false, false, 0}},
          {[10, 0, 0], {true, true, 0}}
        ],
        do: assert(apply(native, :consume_chunks, args) == expected)

    for args <- [[-1, 0, 0], [10, false, 0], [10, 0, 18_446_744_073_709_551_616]],
        do: assert_raise(ArgumentError, fn -> apply(native, :consume_chunks, args) end)

    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/phase_laws.ex"))

    for law <-
          ~w(partial complete completion_closed excess_stays_rejected overflow_rejected empty zero_chunks negative_budget invalid_chunk outside_range)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "phase-laws.export")

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxRecDepth: 8192, maxHeartbeats: 16_000_000]
    ]

    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))

    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 10
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Phase.Properties"],
        module: "Phase.ExportAudit"
      )

    native_export = Path.join(tmp, "phase-native.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: native_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", native_export] ++ sandbox)

    assert status == 0, output

    assert Enum.all?(
             Lynx.Laws.verify([beam], law_options),
             &(&1.status == :ok and &1.cached)
           )

    laws = File.read!(Path.join(workspace, "elixir/phase_laws.ex"))
    incorrect = String.replace(laws, "== {true, true, 7}", "== {true, true, 8}")
    assert incorrect != laws

    [{_, incorrect_beam}] =
      incorrect
      |> String.replace(
        "defmodule LynxPhaseFixture.Laws",
        "defmodule LynxPhaseFixture.FalseLaws"
      )
      |> Code.compile_string("phase_false_laws.ex")

    rejected = Lynx.Laws.verify([incorrect_beam], law_options)
    assert Enum.any?(rejected, &(&1.status == :error))

    assert Enum.any?(Enum.flat_map(rejected, & &1.diagnostics), fn diagnostic ->
             diagnostic[:declaration] == "partial/0" and diagnostic[:severity] == :error
           end)

    for invalid <- [
          "private axiom uncheckedEnumState : False",
          "private theorem unfinishedEnumState : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, properties)

    source = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(source)
    altered = String.replace(original, "*used = total;", "*used = amount;")
    assert altered != original
    File.write!(source, altered)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))

    for type <- ~w(Phase Completion) do
      File.write!(
        source,
        original <>
          "\nimpl Drop for #{type} { fn drop(&mut self) { panic!(\"observable state drop\"); } }\n"
      )

      assert_raise CompileError, ~r/drop|destruct/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(source, original)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok))
  end
end
