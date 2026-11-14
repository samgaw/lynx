defmodule Lynx.Rustler.OwnedResourceHandlesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 3_600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "+owned-drops-v1"
               )
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-drops backend")

  @tag :tmp_dir
  test "proves shared mutex resource behavior across actual Rustler calls and Elixir laws", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Shared"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      workspace: workspace,
      package: "effects-native",
      tools: @tools,
      execution: :runtime,
      owned_drops: true,
      lean_project: project,
      module_prefix: "Shared.Extraction",
      build_dir: Path.join(tmp, "build"),
      cargo: [features: ["locked-resource-handles"]],
      proof_roots: ["effects_native::resource_clone"],
      only: [counter_new: 1, counter_add: 2, counter_value: 1]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "effects_native::CounterResource"}]
           } = prepared.resource_registration

    assert [%{lean_name: "effects_native.CounterResource.drop_owned"}] =
             prepared.verification.resource_cleanup

    assert Enum.any?(
             prepared.bindings.bindings,
             &(&1["name"] == "counter_add" and &1["flags"] == 1)
           )

    adapter = hd(prepared.external.files)["preludes"] |> hd() |> Map.fetch!("source")
    assert String.contains?(adapter, "Lynx.NativeOwnedDrop.drop decoded_arg1")
    assert String.contains?(adapter, "Lynx.NativeOwnedDrop.drop value")

    properties =
      Enum.reduce(
        prepared.bindings.bindings,
        File.read!(Path.join(@fixture, "NativeSharedResourceHandles.lean")),
        fn binding, source ->
          placeholder =
            %{
              "counter_new" => "__CREATE__",
              "counter_add" => "__ADD__",
              "counter_value" => "__READ__"
            }[binding["name"]]

          String.replace(source, placeholder, binding["lean_name"])
        end
      )

    property = Path.join(project, "Shared/Properties.lean")
    File.write!(property, properties)

    File.cp!(
      Path.join(@fixture, "NativeSharedResourceCritical.lean"),
      Path.join(project, "Shared/Critical.lean")
    )

    add_binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == "counter_add"))
    refute Enum.any?(prepared.bindings.bindings, &(&1["name"] == "resource_clone"))

    framed_calls =
      File.read!(Path.join(@fixture, "NativeFramedResourceCalls.lean"))
      |> String.replace("__ADD__", add_binding["lean_name"])

    framed_property = Path.join(project, "Shared/FramedCalls.lean")
    File.write!(framed_property, framed_calls)

    term_adapter =
      File.read!(Path.join(@fixture, "FramedResourceTermAdapter.lean"))
      |> String.replace("__ADD__", add_binding["lean_name"])

    term_adapter_path = Path.join(tmp, "framed-resource-term-adapter.lean")
    File.write!(term_adapter_path, term_adapter)

    options =
      options ++
        [
          proof_modules: ["Shared.Critical", "Shared.Properties", "Shared.FramedCalls"],
          required_properties:
            [
              "Shared.Critical.increment_spec",
              "Shared.Critical.critical_state_handled_next",
              "Shared.Critical.locked_read_handled_next",
              "Shared.FramedCalls.add_call_next",
              "Shared.FramedCalls.decoder_cleanup_next",
              "Shared.FramedCalls.clone_prefix"
            ] ++
              Enum.map(
                ~w(payload_cleanup create_next update_native_handled_next read_native_handled_next add_call_next read_call_next add_safe_call_at add_overflow_call_at update_framed_handled_next read_framed_handled_next Framed.coowned_update),
                &("Shared.Properties." <> &1)
              )
        ]

    load_native(prepared.library, tmp)
    native = LynxEffectsFixture.Native
    resource = apply(native, :counter_new, [7])
    assert is_reference(resource)
    assert apply(native, :counter_add, [resource, 3])
    assert apply(native, :counter_value, [resource]) == 10
    maximum = 18_446_744_073_709_551_615
    largest = apply(native, :counter_new, [maximum])
    refute apply(native, :counter_add, [largest, 1])
    assert apply(native, :counter_value, [largest]) == maximum

    for invalid <- [false, -1, maximum + 1] do
      assert_raise ArgumentError, fn -> apply(native, :counter_add, [resource, invalid]) end
      assert apply(native, :counter_value, [resource]) == 10
    end

    for invalid <- [make_ref(), false, 7],
        do: assert_raise(ArgumentError, fn -> apply(native, :counter_value, [invalid]) end)

    path = Path.join(tmp, "laws.ex")
    laws = File.read!(Path.join(@fixture, "shared_resource_laws.ex"))

    File.write!(path, laws)
    [{_, beam}] = Code.compile_file(path)
    concurrent_path = Path.join(tmp, "concurrent_laws.ex")
    concurrent_laws = File.read!(Path.join(@fixture, "concurrent_resource_laws.ex"))
    File.write!(concurrent_path, concurrent_laws)
    [{_, concurrent_beam}] = Code.compile_file(concurrent_path)
    assert apply(LynxEffectsFixture.ConcurrentResourceLaws, :concurrent_update, [])
    beams = [beam, concurrent_beam]

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 4096],
      debug_dir: Path.join(tmp, "lean-debug")
    ]

    export = Path.join(tmp, "shared-resource.export")
    reports = Lynx.Laws.verify(beams, Keyword.put(law_options, :export, export))

    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify(beams, law_options),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    framed_path = Path.join(tmp, "framed_laws.ex")
    framed_source = File.read!(Path.join(@fixture, "framed_resource_laws.ex"))
    File.write!(framed_path, framed_source)
    framed_beams = Code.compile_file(framed_path)

    for {module, framed_beam} <- framed_beams do
      initial =
        if module == LynxEffectsFixture.FramedResourceLaws,
          do: "Shared.Properties.Framed.initial",
          else: "Shared.Properties.Framed.overflowInitial"

      framed_options = Keyword.put(law_options, :initial_environment, initial)
      framed_export = Path.join(tmp, Atom.to_string(module) <> ".export")

      framed_reports =
        Lynx.Laws.verify([framed_beam], Keyword.put(framed_options, :export, framed_export))

      assert Enum.all?(framed_reports, &(&1.status == :ok)),
             inspect(framed_reports, limit: :infinity)

      assert Enum.all?(
               Lynx.Laws.verify([framed_beam], framed_options),
               &(&1.status == :ok and &1.cached)
             )

      {status, output} =
        Lynx.Commands.lake(project, ["check", "--from-export", framed_export] ++ sandbox)

      assert status == 0, output
    end

    coowned_path = Path.join(tmp, "coowned_laws.ex")
    coowned_source = File.read!(Path.join(@fixture, "coowned_resource_laws.ex"))
    File.write!(coowned_path, coowned_source)
    [{LynxEffectsFixture.CoownedResourceLaws, coowned_beam}] = Code.compile_file(coowned_path)

    coowned_options =
      law_options
      |> Keyword.put(:initial_environment, "Shared.FramedTermAdapter.initial")
      |> Keyword.put(:preludes, [Lynx.Lean.from_file!(term_adapter_path)])

    coowned_export = Path.join(tmp, "coowned-resource.export")

    coowned_reports =
      Lynx.Laws.verify([coowned_beam], Keyword.put(coowned_options, :export, coowned_export))

    assert Enum.all?(coowned_reports, &(&1.status == :ok)),
           inspect(coowned_reports, limit: :infinity)

    assert Enum.any?(
             Enum.flat_map(coowned_reports, &Map.get(&1, :guarantees, [])),
             &match?(
               %{
                 kind: :rust_implementation,
                 rust_name: "effects_native::resource_clone",
                 theorem: "Shared.FramedCalls.clone_prefix"
               },
               &1
             )
           )

    assert Enum.all?(
             Lynx.Laws.verify([coowned_beam], coowned_options),
             &(&1.status == :ok and &1.cached)
           )

    {status, output} =
      Lynx.Commands.lake(project, ["check", "--from-export", coowned_export] ++ sandbox)

    assert status == 0, output

    wrong_contract =
      String.replace(framed_calls, "else cell} ∧", "else (cell.1,cell.2.1,.nil)} ∧",
        global: false
      )

    refute wrong_contract == framed_calls
    File.write!(framed_property, wrong_contract)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(framed_property, framed_calls)

    File.write!(term_adapter_path, term_adapter <> "\nprivate axiom framedAdapterTrust : False\n")

    untrusted_options =
      Keyword.put(coowned_options, :preludes, [Lynx.Lean.from_file!(term_adapter_path)])

    untrusted_reports = Lynx.Laws.verify([coowned_beam], untrusted_options)
    assert Enum.any?(untrusted_reports, &(&1.status == :error)), inspect(untrusted_reports)

    assert Enum.any?(
             Enum.flat_map(untrusted_reports, &Map.get(&1, :diagnostics, [])),
             fn diagnostic ->
               diagnostic.severity == :error and
                 String.contains?(diagnostic.message, "framedAdapterTrust")
             end
           )

    File.write!(term_adapter_path, term_adapter)

    # The postcondition independently checks the other resource's heap payload.
    wrong_frame =
      String.replace(properties, "(heap value 11#u64).all", "(heap value 12#u64).all")

    refute wrong_frame == properties
    File.write!(property, wrong_frame)

    {_, framed_beam} =
      Enum.find(framed_beams, fn {module, _} ->
        module == LynxEffectsFixture.FramedResourceLaws
      end)

    wrong_reports =
      Lynx.Laws.verify(
        [framed_beam],
        Keyword.put(law_options, :initial_environment, "Shared.Properties.Framed.initial")
      )

    assert %{status: :error, diagnostics: frame_diagnostics} =
             Enum.find(
               wrong_reports,
               &(&1.module == "Elixir.LynxEffectsFixture.FramedResourceLaws.laws")
             )

    assert Enum.any?(
             frame_diagnostics,
             &String.contains?(&1.message, "postcondition rejected at a terminal configuration")
           )

    File.write!(property, properties)

    for extra <- [
          "private axiom resourceTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, properties <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, properties)
    wrong = String.replace(laws, "counter_value(resource) == 10", "counter_value(resource) == 11")
    refute wrong == laws
    [{_, wrong_beam}] = Code.compile_string(wrong, path)

    wrong_reports = Lynx.Laws.verify([wrong_beam], law_options)

    assert %{status: :error, diagnostics: wrong_diagnostics} =
             Enum.find(wrong_reports, &(&1.module == "Elixir.LynxEffectsFixture.SharedLaws.laws"))

    assert Enum.any?(
             wrong_diagnostics,
             &match?(%{severity: :error, declaration: "shared_update/0"}, &1)
           )

    refute Enum.any?(wrong_diagnostics, &String.contains?(&1.message, "Unknown identifier"))

    wrong_concurrent =
      String.replace(
        concurrent_laws,
        "counter_value(resource) == 13",
        "counter_value(resource) == 14"
      )

    refute wrong_concurrent == concurrent_laws
    [{_, wrong_concurrent_beam}] = Code.compile_string(wrong_concurrent, concurrent_path)

    wrong_reports = Lynx.Laws.verify([wrong_concurrent_beam], law_options)

    assert %{status: :error, diagnostics: wrong_diagnostics} =
             Enum.find(
               wrong_reports,
               &(&1.module == "Elixir.LynxEffectsFixture.ConcurrentResourceLaws.laws")
             )

    assert Enum.any?(
             wrong_diagnostics,
             &match?(%{severity: :error, declaration: "concurrent_update/0"}, &1)
           )

    refute Enum.any?(wrong_diagnostics, &String.contains?(&1.message, "Unknown identifier"))

    native_source = Path.join(workspace, "native/src/lib.rs")
    native_original = File.read!(native_source)

    wrong_clone =
      String.replace(
        native_original,
        "pub fn resource_clone(\n    resource: &rustler::ResourceArc<CounterResource>,\n) -> rustler::ResourceArc<CounterResource> {\n    resource.clone()\n}",
        "pub fn resource_clone(\n    resource: &rustler::ResourceArc<CounterResource>,\n) -> rustler::ResourceArc<CounterResource> {\n    let _ = resource;\n    resource_new(0)\n}"
      )

    refute wrong_clone == native_original
    File.write!(native_source, wrong_clone)

    error =
      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end

    assert String.contains?(error.message, "Shared/FramedCalls.lean")
    File.write!(native_source, native_original)
    restored = Lynx.Rustler.prepare!(options)
    assert Enum.all?(restored.reports, &(&1.status == :ok))

    core = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(core)

    changed =
      String.replace(
        original,
        "pub fn read_guard(guard: &std::sync::MutexGuard<'_, Counter>) -> u64 {\n    guard.value\n}",
        "pub fn read_guard(guard: &std::sync::MutexGuard<'_, Counter>) -> u64 {\n    guard.value ^ 1\n}"
      )

    refute changed == original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Laws.verify(beams, law_options)
    end

    File.write!(core, original)

    assert_raise CompileError, ~r/resource/, fn ->
      Lynx.Rustler.prepare!(
        options
        |> Keyword.delete(:owned_drops)
        |> Keyword.put(:module_prefix, "Shared.Rejected")
      )
    end
  end

  defp load_native(artifact, tmp) do
    :code.purge(LynxEffectsFixture.Native)
    :code.delete(LynxEffectsFixture.Native)
    :code.purge(LynxEffectsFixture.Native)

    on_exit(fn ->
      :code.delete(LynxEffectsFixture.Native)
      :code.purge(LynxEffectsFixture.Native)
    end)

    library = Path.join(tmp, "shared-resource-native")
    File.cp!(artifact, library <> ".so")
    source = Path.join(tmp, "native.ex")

    File.write!(source, """
    defmodule LynxEffectsFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      def checked(_, _), do: :erlang.nif_error(:not_loaded)
      def released(_, _), do: :erlang.nif_error(:not_loaded)
      def counter_new(_), do: :erlang.nif_error(:not_loaded)
      def counter_add(_, _), do: :erlang.nif_error(:not_loaded)
      def counter_value(_), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxEffectsFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxEffectsFixture.Native)
  end
end
