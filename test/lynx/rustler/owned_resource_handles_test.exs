defmodule Lynx.Rustler.OwnedResourceHandlesTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
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

    options =
      options ++
        [
          proof_modules: ["Shared.Critical", "Shared.Properties"],
          required_properties:
            [
              "Shared.Critical.increment_spec",
              "Shared.Critical.critical_state_handled_next",
              "Shared.Critical.locked_read_handled_next"
            ] ++
              Enum.map(
                ~w(payload_cleanup create_next update_native_handled_next read_native_handled_next add_call_next read_call_next add_safe_call_at add_overflow_call_at),
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
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}),
             &(&1.status == :ok and &1.cached)
           )

    export = Path.join(tmp, "shared-resource.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

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

    assert Enum.any?(
             Lynx.Laws.verify([wrong_beam], native: {Lynx.Rustler, options}),
             &(&1.status == :error)
           )

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
      Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
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
