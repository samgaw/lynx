defmodule Lynx.Rustler.RuntimeCommandsTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_atomics", __DIR__)
  @tools System.get_env("LYNX_NATIVE_COMMANDS_DIR")
  @moduletag timeout: 1_800_000
  unless @tools,
    do: @moduletag(skip: "set LYNX_NATIVE_COMMANDS_DIR for nested tagged native Decoder proofs")

  @tag :tmp_dir
  test "verifies nested tagged commands and rejected requests against native state", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core analysis nif elixir),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    rust = Path.join(workspace, "nif/src/lib.rs")
    File.write!(rust, String.replace(File.read!(rust), "LynxAtomicFixture", "LynxCommandFixture"))
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Commands"))
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
      root_attribute: "lynx::commands",
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Commands.Extraction",
      only: [atomic_new: 1, atomic_read: 1, atomic_command: 2]
    ]

    prepared = Lynx.Rustler.prepare!(common)

    properties =
      Enum.reduce(
        [{"NEW", "atomic_new"}, {"READ", "atomic_read"}, {"COMMAND", "atomic_command"}],
        File.read!(Path.join(@fixture, "CommandProperties.lean")),
        fn {key, name}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, "__#{key}__", binding["lean_name"])
        end
      )

    property = Path.join(project, "Commands/Properties.lean")
    File.write!(property, properties)

    roots =
      ~w(read_decoded replacement_decoded compare_decoded unknown_atom replacement_shape_rejected field_error_callback compare_rejected contract composed current_contract updated read_preserved mismatched nested_rejected_encoded facade_spec facade_new facade_read nested_error_encoded expected_field_error replacement_field_error replacement_expected_error replacement_second_error)

    options =
      common ++
        [
          proof_modules: ["Commands.Properties"],
          required_properties: Enum.map(roots, &("Commands.Properties." <> &1))
        ]

    prepared = Lynx.Rustler.prepare!(options)
    assert Enum.all?(Lynx.Rustler.prepare!(options).reports, &(&1.status == :ok and &1.cached))
    assert Enum.any?(prepared.extraction.encoder_disposals, &(&1.kind == :sdk_string))
    assert Enum.any?(prepared.verification.guarantees, &(&1.kind == :cross_crate_contract))

    assert Enum.any?(prepared.extraction.audit.external_calls, fn {_, model} ->
             model[:native_callback]
           end)

    refute File.exists?(Path.join(project, "Commands/Extraction/FunsExternal_Template.lean"))
    File.mkdir_p!(Path.join(workspace, "priv"))
    File.cp!(prepared.library, Path.join(workspace, "priv/libatomic_nif.so"))

    File.read!(Path.join(workspace, "elixir/native.ex"))
    |> String.replace("LynxAtomicFixture", "LynxCommandFixture")
    |> Code.compile_string(Path.join(workspace, "elixir/native.ex"))

    native = LynxCommandFixture.Native
    resource = apply(native, :atomic_new, [7])
    assert apply(native, :atomic_command, [resource, :read]) == {false, 7}
    assert apply(native, :atomic_command, [resource, {:compare, {7, 11}}]) == {true, 7}
    assert apply(native, :atomic_command, [resource, {:compare, {7, 13}}]) == {false, 11}

    for input <- [{:compare, 0}, {:compare, {true, 3}}, {:compare, {1, false}}] do
      assert catch_error(apply(native, :atomic_command, [resource, input])) ==
               "Could not decode field on position 1"

      assert apply(native, :atomic_read, [resource]) == 11
    end

    assert catch_error(apply(native, :atomic_command, [resource, :unknown])) == :invalid_variant
    [{law_module, beam}] = Code.compile_file(Path.join(workspace, "elixir/command_laws.ex"))

    for law <-
          ~w(read compare mismatch nested_rejection nested_first_field_rejection nested_second_field_rejection nested_range_rejection)a,
        do: assert(apply(law_module, law, []))

    export = Path.join(tmp, "command-laws.export")

    reports =
      Lynx.Laws.verify([beam],
        native: {Lynx.Rustler, options},
        export: export,
        options: [maxRecDepth: 8192, maxHeartbeats: 16_000_000]
      )

    assert [] == for(report <- reports, report.status != :ok, do: report.diagnostics)
    assert length(Enum.flat_map(reports, & &1.theorems)) == 7
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    [adapter | _] = prepared.external.files
    [%{"source" => source}] = adapter["preludes"]

    boundary =
      File.read!(Path.join(@fixture, "CommandBoundary.lean"))
      |> String.replace(
        "__NATIVE__",
        :lynx_core_to_leanj.module_name(String.to_atom(prepared.bindings.module))
      )

    File.write!(Path.join(project, "Commands/Boundary.lean"), source <> "\n" <> boundary)
    Lynx.Rust.Project.build!(project, ["Commands.Boundary"])

    audit =
      Lynx.Rust.Proofs.file!(prepared.extraction, ["Commands.Boundary"],
        module: "Commands.BoundaryAudit"
      )

    boundary_export = Path.join(tmp, "command-boundary.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [audit], export: boundary_export)

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", boundary_export] ++ sandbox)

    assert status == 0, output

    generated = Path.join(project, "Commands/Extraction/Funs.lean")
    original_generated = File.read!(generated)

    without_disposal =
      String.replace(
        original_generated,
        "dispose := fun _ => RustM.ok ()",
        "dispose := fun _ => RustM.fail .undef"
      )

    assert without_disposal != original_generated
    File.write!(generated, without_disposal)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Commands.Properties"])
    end

    File.write!(generated, original_generated)

    for invalid <- [
          "private axiom uncheckedCommand : False",
          "private theorem unfinishedCommand : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> invalid <> "\n")
      assert_raise RuntimeError, ~r/audit/, fn -> Lynx.Rustler.prepare!(options) end
    end

    File.write!(property, properties)
    source = Path.join(workspace, "nif/src/commands.rs")
    original = File.read!(source)

    changed =
      String.replace(
        original,
        "request.expected, request.replacement",
        "request.replacement, request.expected"
      )

    assert changed != original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end
end
