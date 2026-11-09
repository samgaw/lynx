defmodule Lynx.Rustler.FutureResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "pin-as-mut-v1")
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned pin-as-mut backend")

  @tag :tmp_dir
  test "proves actual resource future completion and cancellation through Rustler and Elixir", %{
    tmp_dir: tmp
  } do
    %{
      options: options,
      prepared: prepared,
      workspace: workspace,
      project: project,
      property: property,
      future: future
    } = prepare_fixture(tmp)

    load_native(prepared.library, tmp)
    native = LynxEffectsFixture.Native
    resource = apply(native, :counter_new, [7])
    assert apply(native, :counter_poll_cancel, [resource, 3])
    assert apply(native, :counter_value, [resource]) == 7
    assert apply(native, :counter_poll_add, [resource, 3])
    assert apply(native, :counter_value, [resource]) == 10
    resumed = apply(native, :counter_new, [7])
    assert apply(native, :counter_poll_resume, [resumed, 3])
    assert apply(native, :counter_value, [resumed]) == 10
    maximum = 18_446_744_073_709_551_615
    largest = apply(native, :counter_new, [maximum])
    refute apply(native, :counter_poll_add, [largest, 1])
    refute apply(native, :counter_poll_resume, [largest, 1])
    assert apply(native, :counter_value, [largest]) == maximum

    for function <- [:counter_poll_add, :counter_poll_resume],
        invalid <- [-1, maximum + 1, false] do
      assert_raise ArgumentError, fn -> apply(native, function, [resource, invalid]) end
      assert apply(native, :counter_value, [resource]) == 10
    end

    update_laws =
      File.read!(Path.join(@fixture, "shared_resource_laws.ex"))
      |> String.replace("counter_add", "counter_poll_add")

    cancel_laws = File.read!(Path.join(@fixture, "future_resource_laws.ex"))
    [{_, update_beam}] = Code.compile_string(update_laws, Path.join(tmp, "updates.ex"))
    [{_, cancel_beam}] = Code.compile_string(cancel_laws, Path.join(tmp, "cancel.ex"))

    repeated_laws =
      update_laws
      |> String.replace("LynxEffectsFixture.SharedLaws", "LynxEffectsFixture.RepeatedLaws")
      |> String.replace("counter_poll_add", "counter_poll_resume")
      |> String.replace(
        "Lynx.Rustler.withResourceTypes,",
        "Shared.Future.resume_contract, Lynx.Rustler.withResourceTypes,"
      )

    [{_, repeated_beam}] = Code.compile_string(repeated_laws, Path.join(tmp, "repeated.ex"))
    beams = [update_beam, cancel_beam, repeated_beam]
    reports = Lynx.Laws.verify(beams, native: {Lynx.Rustler, options})
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    export = Path.join(tmp, "future.export")

    assert Enum.all?(
             Lynx.Laws.verify(beams,
               native: {Lynx.Rustler, options},
               export: export
             ),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom futureTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, future <> "\n" <> extra <> "\n")

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property, future)

    wrong =
      String.replace(cancel_laws, "counter_value(resource) == 7", "counter_value(resource) == 10")

    refute wrong == cancel_laws
    [{_, wrong_beam}] = Code.compile_string(wrong, Path.join(tmp, "wrong.ex"))

    assert Enum.any?(
             Lynx.Laws.verify([wrong_beam], native: {Lynx.Rustler, options}),
             &(&1.status == :error)
           )

    source = Path.join(workspace, "native/src/lib.rs")
    rust = File.read!(source)

    for changed <- [
          String.replace(
            rust,
            "std::task::Poll::Pending\n    )",
            "std::task::Poll::Ready(_)\n    )"
          ),
          String.replace(
            rust,
            "std::task::Poll::Pending => future.as_mut().poll(context)",
            "std::task::Poll::Pending => std::task::Poll::Pending"
          )
        ] do
      refute changed == rust
      File.write!(source, changed)

      assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(source, rust)

    assert Enum.all?(
             Lynx.Laws.verify(beams, native: {Lynx.Rustler, options}),
             &(&1.status == :ok)
           )
  end

  @tag :tmp_dir
  test "proves concurrent complete future calls through compiled Rustler bindings", %{
    tmp_dir: tmp
  } do
    %{options: options, prepared: prepared, project: project} = prepare_fixture(tmp)
    load_native(prepared.library, tmp)

    laws =
      File.read!(Path.join(@fixture, "concurrent_resource_laws.ex"))
      |> String.replace("ConcurrentResourceLaws", "ConcurrentFutureLaws")
      |> String.replace("counter_add", "counter_poll_resume")

    path = Path.join(tmp, "concurrent_future_laws.ex")
    [{LynxEffectsFixture.ConcurrentFutureLaws, beam}] = Code.compile_string(laws, path)
    assert apply(LynxEffectsFixture.ConcurrentFutureLaws, :concurrent_update, [])

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxHeartbeats: 16_000_000, maxRecDepth: 4096],
      debug_dir: Path.join(tmp, "lean-debug")
    ]

    export = Path.join(tmp, "concurrent-future.export")
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
    assert Enum.any?(Lynx.Laws.verify([wrong_beam], law_options), &(&1.status == :error))
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
      cargo: [features: ["future-resource-handles"]],
      only: [
        counter_new: 1,
        counter_poll_add: 2,
        counter_poll_cancel: 2,
        counter_poll_resume: 2,
        counter_value: 1
      ]
    ]

    prepared = Lynx.Rustler.prepare!(options)
    assert prepared.resource_registration.status == :validated_configuration
    assert Enum.any?(prepared.extraction.native_unwind, &(&1.kind == :constant_cleanup_branch))
    assert Enum.any?(prepared.verification.external_models, &String.contains?(&1, "Waker::noop"))

    names = Map.new(prepared.bindings.bindings, &{&1["name"], &1["lean_name"]})

    fill = fn source ->
      Enum.reduce(
        [
          {"__CREATE__", "counter_new"},
          {"__ADD__", "counter_poll_add"},
          {"__CANCEL__", "counter_poll_cancel"},
          {"__RESUME__", "counter_poll_resume"},
          {"__READ__", "counter_value"}
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

    future = fill.(File.read!(Path.join(@fixture, "NativeResourcePoll.lean")))
    property = Path.join(project, "Shared/Future.lean")
    File.write!(property, future)

    shared =
      File.read!(Path.join(@fixture, "NativeSharedResourceHandles.lean"))
      |> String.replace(
        "public import Shared.Critical",
        "public import Shared.Critical\npublic import Shared.Future"
      )
      |> String.replace(
        "Rustler.executeNative, __ADD__,",
        "Rustler.executeNative, Shared.Future.add_contract,"
      )
      |> fill.()

    File.write!(Path.join(project, "Shared/Properties.lean"), shared)

    File.write!(
      Path.join(project, "Shared/PollProperties.lean"),
      fill.(File.read!(Path.join(@fixture, "NativeResourcePollHandles.lean")))
    )

    options =
      options ++
        [
          proof_modules: [
            "Shared.Critical",
            "Shared.Future",
            "Shared.Properties",
            "Shared.PollProperties"
          ],
          required_properties:
            Enum.map(
              ~w(ready_poll ready_drop add_contract pending_poll pending_drop cancel_contract resumed_poll completed_drop finish_contract resume_contract),
              &("Shared.Future." <> &1)
            ) ++
              [
                "Shared.Critical.increment_spec",
                "Shared.Critical.critical_state_handled_next",
                "Shared.Critical.locked_read_handled_next",
                "Shared.Properties.add_call_next",
                "Shared.Properties.read_call_next",
                "Shared.PollProperties.cancel_call_next",
                "Shared.PollProperties.cancel_call_at"
              ]
        ]

    %{
      options: options,
      prepared: prepared,
      workspace: workspace,
      project: project,
      property: property,
      future: future
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

    library = Path.join(tmp, "future-resource-native")
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
      def counter_poll_add(_, _), do: :erlang.nif_error(:not_loaded)
      def counter_poll_cancel(_, _), do: :erlang.nif_error(:not_loaded)
      def counter_poll_resume(_, _), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxEffectsFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxEffectsFixture.Native)
  end
end
