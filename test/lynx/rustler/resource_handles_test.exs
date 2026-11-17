defmodule Lynx.Rustler.ResourceHandlesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "effectful-calls-v1"
               )
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned resource backend")

  @tag :tmp_dir
  test "proves resources across separate NIF calls", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, ".lake"))
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
    if File.dir?(packages), do: File.ln_s!(packages, Path.join(project, ".lake/packages"))

    options = [
      workspace: workspace,
      package: "effects-native",
      tools: @tools,
      execution: :runtime,
      lean_project: project,
      module_prefix: "Handles.Extraction",
      build_dir: Path.join(tmp, "build"),
      cargo: [features: ["resource-handles"]],
      only: [resource_create: 1, resource_value: 1, resource_checked: 2]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert_raise ArgumentError, ~r/validated registration/, fn ->
      Lynx.Rustler.Bindings.link!(
        prepared.bindings,
        prepared.extraction.audit,
        prepared.extraction.translation,
        result_monad: "Lynx.NativeM",
        resource_types: []
      )
    end

    assert_raise ArgumentError, ~r/runtime execution/, fn ->
      Lynx.Rustler.Adapter.external!(prepared.bindings, prepared.extraction.implementations,
        execution: :pure,
        bridge_module: "Handles.RustlerBridge",
        implementation_module: "Handles.InvalidAdapter"
      )
    end

    property = Path.join(project, "Handles/Properties.lean")
    bindings = Map.new(prepared.bindings.bindings, &{&1["name"], &1["lean_name"]})

    File.write!(
      property,
      File.read!(Path.join(@fixture, "NativeResourceHandles.lean"))
      |> String.replace("__CREATE__", bindings["resource_create"])
      |> String.replace("__READ__", bindings["resource_value"])
      |> String.replace("__CHECKED__", bindings["resource_checked"])
    )

    options =
      options ++
        [
          proof_modules: ["Handles.Properties"],
          required_properties:
            Enum.map(
              ~w(reader resource_reader checked_reader checked_disabled create_continuation read_continuation create_framed_continuation read_pinned_continuation),
              &("Handles.Properties." <> &1)
            )
        ]

    load_native(prepared.library, tmp)
    resource = apply(LynxEffectsFixture.Native, :resource_create, [7])
    assert is_reference(resource)
    assert apply(LynxEffectsFixture.Native, :resource_value, [resource]) == 7
    largest = 18_446_744_073_709_551_615
    large_resource = apply(LynxEffectsFixture.Native, :resource_create, [largest])
    assert apply(LynxEffectsFixture.Native, :resource_value, [large_resource]) == largest

    for invalid <- [-1, largest + 1],
        do:
          assert_raise(ArgumentError, fn ->
            apply(LynxEffectsFixture.Native, :resource_create, [invalid])
          end)

    assert apply(LynxEffectsFixture.Native, :resource_checked, [resource, true]) == 7
    assert apply(LynxEffectsFixture.Native, :resource_checked, [resource, false]) == 0

    assert_raise ArgumentError, fn ->
      apply(LynxEffectsFixture.Native, :resource_checked, [resource, 0])
    end

    assert apply(LynxEffectsFixture.Native, :resource_value, [resource]) == 7

    for value <- [false, 7, make_ref()],
        do:
          assert_raise(ArgumentError, fn ->
            apply(LynxEffectsFixture.Native, :resource_value, [value])
          end)

    source = Path.join(tmp, "laws.ex")
    File.write!(source, laws())
    [{_, beam}] = Code.compile_file(source)

    law_options = [
      native: {Lynx.Rustler, options},
      options: [maxHeartbeats: 4_000_000]
    ]

    reports = Lynx.Laws.verify([beam], law_options)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.any?(prepared.verification.external_models, &String.contains?(&1, "VM resource"))
    warm = Lynx.Laws.verify([beam], law_options)
    assert Enum.all?(warm, &(&1.status == :ok && &1.cached))
    export = Path.join(tmp, "handles.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], Keyword.put(law_options, :export, export)),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
    original_properties = File.read!(property)

    broken_frame =
      String.replace(
        original_properties,
        "(env.nativeRefCounter + 4) ++ env.nativeHeap}",
        "(env.nativeRefCounter + 4)}",
        global: false
      )

    refute broken_frame == original_properties
    File.write!(property, broken_frame)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Handles.Properties"])
    end

    File.write!(property, original_properties)

    core = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(core)

    changed =
      String.replace(original, "    counter.value\n}", "    counter.value ^ 1\n}", global: false)

    refute changed == original
    File.write!(core, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Laws.verify([beam], law_options)
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

    library = Path.join(tmp, "resource-handles-native")
    File.cp!(artifact, library <> ".so")
    source = Path.join(tmp, "native.ex")

    File.write!(source, """
    defmodule LynxEffectsFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      def checked(_, _), do: :erlang.nif_error(:not_loaded)
      def released(_, _), do: :erlang.nif_error(:not_loaded)
      def retained(_), do: :erlang.nif_error(:not_loaded)
      def resource_create(_), do: :erlang.nif_error(:not_loaded)
      def resource_value(_), do: :erlang.nif_error(:not_loaded)
      def resource_checked(_, _), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxEffectsFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(source, tmp, LynxEffectsFixture.Native)
  end

  defp laws do
    ~S'''
    defmodule LynxEffectsFixture.HandleLaws do
      @compile :debug_info
      use Lynx.Laws
      law roundtrip,
        expects: LynxEffectsFixture.Native.resource_value(LynxEffectsFixture.Native.resource_create(7)) == 7,
        proof: ~LEAN"""
        refine ⟨0, ?_⟩
        intro depth enough elapsed events last outcome run terminal
        apply terminal.outcome_eq.symm.trans
        apply Lynx.Outcome.eq_of_isTrue
        apply Lynx.Concurrent.checkPost_sound (depth := 64)
          (accept := fun config => config.outcome.isTrue) ?_ run terminal
        clear enough events last outcome run terminal
        lynx_check_post
        """
      law failure_cleanup,
        expects: (
          resource = LynxEffectsFixture.Native.resource_create(7)
          caught = try do
            LynxEffectsFixture.Native.resource_checked(resource, 0)
            false
          catch
            :error, :badarg -> true
          end
          caught and LynxEffectsFixture.Native.resource_value(resource) == 7
        ),
        proof: ~LEAN"""
        refine ⟨0, ?_⟩
        intro depth enough elapsed events last outcome run terminal
        apply terminal.outcome_eq.symm.trans
        apply Lynx.Outcome.eq_of_isTrue
        apply Lynx.Concurrent.checkPost_sound (depth := 64)
          (accept := fun config => config.outcome.isTrue) ?_ run terminal
        clear enough events last outcome run terminal
        lynx_check_post
        """
      law two_resources,
        expects: (
          first = LynxEffectsFixture.Native.resource_create(7)
          second = LynxEffectsFixture.Native.resource_create(9)
          LynxEffectsFixture.Native.resource_value(first) == 7 and
            LynxEffectsFixture.Native.resource_value(second) == 9
        ),
        proof: ~LEAN"""
        refine ⟨0, ?_⟩
        intro depth enough elapsed events last outcome run terminal
        apply terminal.outcome_eq.symm.trans
        apply Lynx.Outcome.eq_of_isTrue
        apply Lynx.Concurrent.checkPost_sound (depth := 64)
          (accept := fun config => config.outcome.isTrue) ?_ run terminal
        clear enough events last outcome run terminal
        lynx_check_post
        """
    end
    '''
  end
end
