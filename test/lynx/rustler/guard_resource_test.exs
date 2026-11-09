defmodule Lynx.Rustler.GuardResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "owned-captures-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned owned-captures backend")

  @tag :tmp_dir
  test "proves saved resource and guard cleanup through compiled Rustler calls", %{tmp_dir: tmp} do
    %{
      options: options,
      prepared: prepared,
      project: project,
      property: property,
      original: original,
      workspace: workspace
    } = prepare_fixture(tmp)

    load_native(prepared.library, tmp)
    native = LynxEffectsFixture.Native
    maximum = 18_446_744_073_709_551_615

    for function <- [:counter_guard_finish, :counter_guard_cancel] do
      resource = apply(native, :counter_new, [7])
      assert apply(native, function, [resource, 3])
      assert apply(native, :counter_value, [resource]) == 10
      largest = apply(native, :counter_new, [maximum])
      assert apply(native, function, [largest, 1]) == (function == :counter_guard_cancel)
      assert apply(native, :counter_value, [largest]) == maximum

      for invalid <- [-1, maximum + 1, false] do
        assert_raise ArgumentError, fn -> apply(native, function, [resource, invalid]) end
        assert apply(native, :counter_value, [resource]) == 10
      end
    end

    raw = JSON.decode!(File.read!(prepared.extraction.llbc))

    assert_raise ArgumentError, ~r/saved guard requires the validated NativeGuard/, fn ->
      Lynx.Rust.NativeGuardStorage.lower!(raw, prepared.extraction.audit, [], :cancelling)
    end

    assert [%{representation: :native_guard_capability}] =
             prepared.extraction.native_guard_storage

    source = File.read!(Path.join(@fixture, "shared_resource_laws.ex"))

    finish =
      source
      |> String.replace("SharedLaws", "GuardedFinishLaws")
      |> String.replace("counter_add", "counter_guard_finish")

    cancel =
      source
      |> String.replace("SharedLaws", "GuardedCancelLaws")
      |> String.replace("counter_add", "counter_guard_cancel")
      |> String.replace(
        "counter_guard_cancel(resource, 1) == false",
        "counter_guard_cancel(resource, 1) == true"
      )

    [{_, finish_beam}] = Code.compile_string(finish, Path.join(tmp, "finish.ex"))
    [{_, cancel_beam}] = Code.compile_string(cancel, Path.join(tmp, "cancel.ex"))
    beams = [finish_beam, cancel_beam]
    export = Path.join(tmp, "guard-resource.export")
    reports = Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}, export: export)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    wrong =
      String.replace(cancel, "counter_value(resource) == 10", "counter_value(resource) == 7")

    refute wrong == cancel
    [{_, wrong_beam}] = Code.compile_string(wrong, Path.join(tmp, "wrong.ex"))
    wrong_reports = Lynx.Laws.verify([wrong_beam], native: {Lynx.Rustler, options})

    assert %{status: :error, diagnostics: diagnostics} =
             Enum.find(
               wrong_reports,
               &(&1.module == "Elixir.LynxEffectsFixture.GuardedCancelLaws.laws")
             )

    assert Enum.any?(
             diagnostics,
             &match?(%{severity: :error, declaration: "shared_update/0"}, &1)
           )

    refute Enum.any?(diagnostics, &String.contains?(&1.message, "Unknown identifier"))

    for extra <- [
          "private axiom guardTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, original)

    native_source = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native_source)

    changed =
      String.replace(
        source,
        "let changed = effects_core::increment_guard(&mut guard, amount);\n    let _progress = effects_core::paused_counter(amount).await;\n    effects_core::release_guard(guard);\n    resource_release(resource);",
        "let changed = effects_core::increment_guard(&mut guard, 0);\n    let _progress = effects_core::paused_counter(amount).await;\n    effects_core::release_guard(guard);\n    resource_release(resource);",
        global: false
      )

    refute source == changed
    File.write!(native_source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(native_source, source)
    assert %{verification: %{guarantees: [_ | _]}} = Lynx.Rustler.prepare!(options)
  end

  @tag :tmp_dir
  test "composes concurrent cancellation of actual guard-holding resource futures", %{
    tmp_dir: tmp
  } do
    %{options: options, prepared: prepared, project: project} = prepare_fixture(tmp)
    load_native(prepared.library, tmp)

    laws =
      File.read!(Path.join(@fixture, "concurrent_resource_laws.ex"))
      |> String.replace("ConcurrentResourceLaws", "ConcurrentGuardLaws")
      |> String.replace("counter_add", "counter_guard_cancel")

    path = Path.join(tmp, "concurrent_guard_laws.ex")
    [{LynxEffectsFixture.ConcurrentGuardLaws, beam}] = Code.compile_string(laws, path)
    assert apply(LynxEffectsFixture.ConcurrentGuardLaws, :concurrent_update, [])

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 4096],
      debug_dir: Path.join(tmp, "lean-debug")
    ]

    export = Path.join(tmp, "concurrent-guard.export")
    reports = Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export))
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(Lynx.Laws.verify([beam], law_options), &(&1.status == :ok and &1.cached))
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    wrong = String.replace(laws, "counter_value(resource) == 13", "counter_value(resource) == 14")
    refute wrong == laws
    [{_, wrong_beam}] = Code.compile_string(wrong, path)
    reports = Lynx.Laws.verify([wrong_beam], law_options)

    assert %{status: :error, diagnostics: diagnostics} =
             Enum.find(
               reports,
               &(&1.module == "Elixir.LynxEffectsFixture.ConcurrentGuardLaws.laws")
             )

    assert Enum.any?(
             diagnostics,
             &match?(%{severity: :error, declaration: "concurrent_update/0"}, &1)
           )

    refute Enum.any?(diagnostics, &String.contains?(&1.message, "Unknown identifier"))
  end

  defp prepare_fixture(tmp) do
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
      futures: :cancelling,
      owned_drops: true,
      lean_project: project,
      module_prefix: "Shared.Extraction",
      build_dir: Path.join(tmp, "build"),
      cargo: [features: ["guard-future-resource-handles"]],
      only: [
        counter_new: 1,
        counter_add: 2,
        counter_value: 1,
        counter_guard_finish: 2,
        counter_guard_cancel: 2
      ]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    names = Map.new(prepared.bindings.bindings, &{&1["name"], &1["lean_name"]})

    fill = fn source ->
      Enum.reduce(
        [
          {"__CREATE__", "counter_new"},
          {"__ADD__", "counter_add"},
          {"__READ__", "counter_value"},
          {"__FINISH__", "counter_guard_finish"},
          {"__CANCEL__", "counter_guard_cancel"}
        ],
        source,
        fn {placeholder, name}, source ->
          String.replace(source, placeholder, Map.fetch!(names, name))
        end
      )
    end

    File.cp!(
      Path.join(@fixture, "NativeSharedResourceCritical.lean"),
      Path.join(project, "Shared/Critical.lean")
    )

    File.write!(
      Path.join(project, "Shared/Properties.lean"),
      fill.(File.read!(Path.join(@fixture, "NativeSharedResourceHandles.lean")))
    )

    original = fill.(File.read!(Path.join(@fixture, "NativeGuardResource.lean")))
    property = Path.join(project, "Shared/Guarded.lean")
    File.write!(property, original)

    options =
      options ++
        [
          proof_modules: ["Shared.Critical", "Shared.Properties", "Shared.Guarded"],
          required_properties:
            ["Shared.Critical.increment_spec", "Shared.Properties.add_call_next"] ++
              Enum.map(
                ~w(first_poll resumed_poll pending_drop initial_drop completed_drop finish_driver cancel_driver finish_contract cancel_contract),
                &("Shared.Guarded." <> &1)
              )
        ]

    %{
      options: options,
      prepared: prepared,
      project: project,
      property: property,
      original: original,
      workspace: workspace
    }
  end

  defp load_native(artifact, tmp) do
    :code.purge(LynxEffectsFixture.Native)
    :code.delete(LynxEffectsFixture.Native)
    :code.purge(LynxEffectsFixture.Native)

    on_exit(fn ->
      :code.delete(LynxEffectsFixture.Native)
      :code.purge(LynxEffectsFixture.Native)
    end)

    library = Path.join(tmp, "guard-resource-native")
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
      def counter_guard_finish(_, _), do: :erlang.nif_error(:not_loaded)
      def counter_guard_cancel(_, _), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxEffectsFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxEffectsFixture.Native)
  end
end
