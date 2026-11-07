defmodule Lynx.Rustler.RuntimeTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR for native runtime NIF proofs")

  @tag :tmp_dir
  test "composes actual native critical sections and failures into Elixir laws", %{tmp_dir: tmp} do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "RuntimeNif"))
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
      lean_project: project,
      module_prefix: "RuntimeNif.Extraction",
      build_dir: Path.join(tmp, "build"),
      cargo: [features: ["nif"]]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert_raise CompileError, fn ->
      Lynx.Rustler.prepare!(
        Keyword.merge(options, execution: :pure, module_prefix: "RuntimeNif.RejectedPure")
      )
    end

    assert prepared.verification.execution == :runtime
    assert Enum.all?(prepared.external.purities, fn {_, purity} -> purity == :concurrent end)
    audit = prepared.extraction.audit

    cutoff_models =
      Enum.filter(audit.external_calls, fn {_, model} -> model[:native_cutoff_only] end)

    assert length(cutoff_models) == 3

    assert Enum.count(
             prepared.verification.unverified_external_calls,
             &(&1[:native_cutoff_only] == true)
           ) == 3

    without_cutoffs =
      Map.new(audit.external_calls, fn {id, model} ->
        {id, Map.delete(model, :native_cutoff_only)}
      end)

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      Lynx.Rust.NativeLifetimes.audit!(
        audit.functions,
        without_cutoffs,
        audit.translated,
        audit.references
      )
    end

    assert Enum.any?(prepared.bindings.bindings, &(&1["name"] == "checked" && &1["flags"] == 1))

    properties = File.read!(Path.join(@fixture, "NativeRustler.lean"))

    properties =
      Enum.reduce(
        [{"checked", "__CHECKED__"}, {"released", "__RELEASED__"}],
        properties,
        fn {name, placeholder}, source ->
          binding = Enum.find(prepared.bindings.bindings, &(&1["name"] == name))
          String.replace(source, placeholder, binding["lean_name"])
        end
      )

    property_path = Path.join(project, "RuntimeNif/Properties.lean")
    File.write!(property_path, properties)

    options =
      options ++
        [
          proof_modules: ["RuntimeNif.Properties"],
          required_properties:
            Enum.map(
              ~w(increment_spec internal_state facade_adapter_continuation released_adapter_continuation released_handler_continuation released_handler_prefix),
              &("RuntimeNif.Properties." <> &1)
            )
        ]

    load_native(prepared, tmp)
    native = LynxEffectsFixture.Native
    assert apply(native, :checked, [7, 3])
    refute apply(native, :checked, [18_446_744_073_709_551_615, 1])
    assert apply(native, :checked, [18_446_744_073_709_551_615, 0])
    assert apply(native, :released, [7, true])
    assert catch_error(apply(native, :released, [7, false])) == :nif_panicked

    for args <- [[-1, 0], [18_446_744_073_709_551_616, 0], [false, 0]],
        do: assert_raise(ArgumentError, fn -> apply(native, :checked, args) end)

    path = Path.join(tmp, "laws.ex")
    File.write!(path, laws())
    [{_, beam}] = Code.compile_file(path)
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})

    errors =
      for report <- reports,
          report.status != :ok,
          do: %{module: report.module, diagnostics: report.diagnostics}

    assert errors == [], inspect(errors, limit: :infinity)
    guarantees = Enum.flat_map(reports, &Map.get(&1, :guarantees, []))

    for kind <- [:rust_implementation, :cross_crate_contract, :nif_adapter, :elixir_law],
        do: assert(Enum.any?(guarantees, &(&1.kind == kind)))

    warm = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options})
    assert Enum.all?(warm, &(&1.status == :ok && &1.cached)), inspect(warm, limit: :infinity)
    export = Path.join(tmp, "runtime.export")

    assert Enum.all?(
             Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export),
             &(&1.status == :ok)
           )

    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for fragment <- [
          "\nprivate axiom unexpected_native : False\n",
          "\nprivate theorem unfinished_native : False := by sorry\n"
        ] do
      File.write!(property_path, properties <> fragment)

      assert_raise RuntimeError, ~r/native adapter or proof audit failed/, fn ->
        Lynx.Rustler.prepare!(options)
      end
    end

    File.write!(property_path, properties)

    wrong =
      String.replace(
        properties,
        "changed = decide (value.val + amount.val ≤ U64.max) := by",
        "changed = true := by"
      )

    refute wrong == properties
    File.write!(property_path, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(property_path, properties)

    source = Path.join(workspace, "core/src/lib.rs")
    original = File.read!(source)

    changed =
      String.replace(original, "increment(&mut counter, amount);", "increment(&mut counter, 0);")

    refute changed == original
    File.write!(source, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rustler.prepare!(options)
    end

    File.write!(
      source,
      String.replace(
        original,
        "    *guard = counter.value;",
        "    assert!(false);\n    *guard = counter.value;"
      )
    )

    assert_raise CompileError, ~r/native owner lifetime|structural drop erasure rejected/, fn ->
      Lynx.Rustler.prepare!(options)
    end
  end

  defp load_native(prepared, tmp) do
    library = Path.join(tmp, "native")
    File.cp!(prepared.library, library <> ".so")
    path = Path.join(tmp, "native.ex")

    File.write!(path, """
    defmodule LynxEffectsFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      def checked(_value, _amount), do: :erlang.nif_error(:not_loaded)
      def released(_value, _accepted), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxEffectsFixture.Native], _} =
             Lynx.Rustler.NifFixture.compile!(path, tmp, LynxEffectsFixture.Native)
  end

  defp laws do
    ~S'''
    defmodule LynxEffectsFixture.Laws do
      @compile :debug_info
      use Lynx.Laws
      law successful_update,
        expects: LynxEffectsFixture.Native.checked(7, 3) == true,
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «successful_update:ensures/0», Elixir.LynxEffectsFixture.Native.«checked/2»,
          Elixir.LynxEffectsFixture.Native.«checked:execution/2», Lynx.Rustler.decodeUnsigned,
          Lynx.Result.ofExcept, RuntimeNif.Properties.facade_adapter_continuation,
          Lynx.Rustler.encodeBool, Erlang.erlang.«==/2», Aeneas.Std.U64.max,
          Aeneas.Std.UScalar.val, Aeneas.Std.U64.numBits]
        """
      law overflow_rejected,
        expects: LynxEffectsFixture.Native.checked(18446744073709551615, 1) == false,
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «overflow_rejected:ensures/0», Elixir.LynxEffectsFixture.Native.«checked/2»,
          Elixir.LynxEffectsFixture.Native.«checked:execution/2», Lynx.Rustler.decodeUnsigned,
          Lynx.Result.ofExcept, RuntimeNif.Properties.facade_adapter_continuation,
          Lynx.Rustler.encodeBool, Erlang.erlang.«==/2», Aeneas.Std.U64.max,
          Aeneas.Std.UScalar.val, Aeneas.Std.U64.numBits]
        """
      law repeated_checks,
        expects: LynxEffectsFixture.Native.checked(7, 3) == true and
          LynxEffectsFixture.Native.checked(18446744073709551615, 1) == false,
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «repeated_checks:ensures/0», Elixir.LynxEffectsFixture.Native.«checked/2»,
          Elixir.LynxEffectsFixture.Native.«checked:execution/2», Lynx.Rustler.decodeUnsigned,
          Lynx.Result.ofExcept, RuntimeNif.Properties.facade_adapter_continuation,
          Lynx.Rustler.encodeBool, Erlang.erlang.«==/2», Aeneas.Std.U64.max,
          Aeneas.Std.UScalar.val, Aeneas.Std.U64.numBits]
        """
      law badarg,
        expects: (try do LynxEffectsFixture.Native.checked(-1, 0) catch :error, :badarg -> true end),
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «badarg:ensures/0», Elixir.LynxEffectsFixture.Native.«checked/2»,
          Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        """
      law panic_after_cleanup,
        expects: (try do LynxEffectsFixture.Native.released(7, false); false catch :error, :nif_panicked -> true end),
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «panic_after_cleanup:ensures/0», Elixir.LynxEffectsFixture.Native.«released/2»,
          Elixir.LynxEffectsFixture.Native.«released:execution/2», Lynx.Rustler.decodeUnsigned,
          Lynx.Rustler.decodeBool, Lynx.Result.ofExcept, RuntimeNif.Properties.released_handler_prefix,
          Lynx.Exception.classTerm, Lynx.Exception.reason]
        """
    end
    '''
  end
end
