defmodule Lynx.Rustler.ResourceTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "global-names-v1"
               )
  unless @available, do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned resource backend")

  @tag :tmp_dir
  test "proves Elixir laws through compiled registration and actual resource implementations", %{
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
      module_prefix: "Resource.Facade",
      build_dir: Path.join(tmp, "build"),
      cargo: [features: ["resource-nif"]],
      only: [retained: 1]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert %{
             status: :validated_configuration,
             types: [%{rust_name: "effects_native::ScalarResource"}],
             inventory: inventory
           } = prepared.resource_registration

    assert length(inventory) == 2
    registration = prepared.resource_registration
    document = JSON.decode!(File.read!(registration.compiler_file))

    for operation <- ~w(register_all_collected new) do
      changed =
        update_in(document, ["translated", "fun_decls"], fn functions ->
          Enum.map(functions, fn f ->
            if f && List.last(f["item_meta"]["name"]) == %{"Ident" => [operation, 0]},
              do: put_in(f, ["signature", "is_unsafe"], true),
              else: f
          end)
        end)

      assert_raise ArgumentError, fn ->
        Lynx.Rustler.Registrations.resolve!(registration.metadata, changed, "effects_native")
      end
    end

    assert_raise ArgumentError, ~r/no resource load callback/, fn ->
      Lynx.Rustler.Metadata.resources!(prepared.expanded, %{load: false}, "effects_native")
    end

    assert Enum.any?(
             prepared.verification.trusted_boundary,
             &String.contains?(&1, "registration execution")
           )

    [binding] = prepared.bindings.bindings
    property = Path.join(project, "Resource/Properties.lean")

    File.write!(
      property,
      File.read!(Path.join(@fixture, "NativeResourceRustler.lean"))
      |> String.replace("__NIF__", binding["lean_name"])
    )

    options =
      options ++
        [
          proof_modules: ["Resource.Properties"],
          required_properties:
            Enum.map(
              ~w(reader resource_reader facade_continuation),
              &("Resource.Properties." <> &1)
            )
        ]

    load_native(prepared.library, tmp)
    assert apply(LynxEffectsFixture.Native, :retained, [7]) == 7

    assert apply(LynxEffectsFixture.Native, :retained, [18_446_744_073_709_551_615]) ==
             18_446_744_073_709_551_615

    for input <- [-1, 18_446_744_073_709_551_616, false],
        do:
          assert_raise(ArgumentError, fn ->
            apply(LynxEffectsFixture.Native, :retained, [input])
          end)

    source = Path.join(tmp, "laws.ex")
    File.write!(source, laws())
    [{_, beam}] = Code.compile_file(source)
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    warm = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
    assert Enum.all?(warm, &(&1.status == :ok && &1.cached)), inspect(warm, limit: :infinity)
    export = Path.join(tmp, "resource.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    native = Path.join(workspace, "native/src/lib.rs")
    original = File.read!(native)

    File.write!(
      native,
      String.replace(
        original,
        "#[rustler::resource_impl]\nimpl rustler::Resource for ScalarResource",
        "#[rustler::resource_impl(register = false)]\nimpl rustler::Resource for ScalarResource"
      )
    )

    assert_raise ArgumentError, ~r/missing or ambiguous compiled resource registration/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(
      native,
      String.replace(
        original,
        "rustler::init!(\"Elixir.LynxEffectsFixture.Native\");",
        "fn custom_load(_: rustler::Env<'_>, _: rustler::Term<'_>) -> bool { true }\nrustler::init!(\"Elixir.LynxEffectsFixture.Native\", load = custom_load);"
      )
    )

    assert_raise ArgumentError,
                 ~r/generated Rustler 0.39 loader without a custom load callback/,
                 fn ->
                   Lynx.Rustler.prepare!(options)
                 end
  end

  defp load_native(artifact, tmp) do
    library = Path.join(tmp, "resource-native")
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
    end
    """)

    assert {:ok, [LynxEffectsFixture.Native], _} =
             Kernel.ParallelCompiler.compile_to_path([source], tmp, return_diagnostics: true)
  end

  defp laws do
    ~S'''
    defmodule LynxEffectsFixture.ResourceLaws do
      @compile :debug_info
      use Lynx.Laws
      law retained_value,
        expects: LynxEffectsFixture.Native.retained(7) == 7,
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «retained_value:ensures/0», Elixir.LynxEffectsFixture.Native.«retained/1»,
          Elixir.LynxEffectsFixture.Native.«retained:execution/1», Lynx.Rustler.withResourceTypes,
          Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept,
          Lynx.NativeResourceArc.typeName, Erlang.erlang.«==/2»,
          Aeneas.Std.U64.max, Aeneas.Std.UScalar.val, Aeneas.Std.U64.numBits]
        rw [Resource.Properties.facade_continuation]
        all_goals simp [Lynx.NativeResourceArc.typeName, Aeneas.Std.UScalar.val]
        """
      law repeated_retains,
        expects: LynxEffectsFixture.Native.retained(LynxEffectsFixture.Native.retained(7)) == 7,
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «repeated_retains:ensures/0», Elixir.LynxEffectsFixture.Native.«retained/1»,
          Elixir.LynxEffectsFixture.Native.«retained:execution/1», Lynx.Rustler.withResourceTypes,
          Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept,
          Lynx.NativeResourceArc.typeName, Erlang.erlang.«==/2»,
          Aeneas.Std.U64.max, Aeneas.Std.UScalar.val, Aeneas.Std.U64.numBits]
        rw [Resource.Properties.facade_continuation]
        · simp [Lynx.Rustler.withResourceTypes, Lynx.Rustler.decodeUnsigned,
            Lynx.Result.ofExcept, Aeneas.Std.U64.max, Aeneas.Std.UScalar.val, Aeneas.Std.U64.numBits]
          rw [Resource.Properties.facade_continuation]
          all_goals simp [Lynx.NativeResourceArc.typeName, Aeneas.Std.UScalar.val]
        · simp [Lynx.NativeResourceArc.typeName]
        · rfl
        """
      law badarg,
        expects: (try do LynxEffectsFixture.Native.retained(-1) catch :error, :badarg -> true end),
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «badarg:ensures/0», Elixir.LynxEffectsFixture.Native.«retained/1»,
          Lynx.Rustler.withResourceTypes, Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept,
          Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        """
    end
    '''
  end
end
