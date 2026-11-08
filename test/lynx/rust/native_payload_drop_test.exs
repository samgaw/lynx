defmodule Lynx.Rust.NativePayloadDropTest do
  use ExUnit.Case
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 600_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(File.read!(Path.join(@tools, "lynx-toolchain")), "needs-drop-v1")
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned compiler-drop-query backend")

  @tag :tmp_dir
  test "proves compiler-certified struct cleanup and rejects real user destructors", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Runtime"))

    File.cp!(
      Path.join(@fixture, "NativePayloadDrop.lean"),
      Path.join(project, "Runtime/PayloadProperties.lean")
    )

    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    opts = [
      roots: Enum.map(~w(mutex_discard mutex_scope mutex_assert), &("effects_native::" <> &1)),
      execution: :runtime,
      unwind: :assertions,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Runtime.Payload",
      proof_modules: ["Runtime.PayloadProperties"],
      required_properties:
        Enum.map(
          ~w(explicit_dispose scope_dispose assertion_cleanup),
          &("Runtime.PayloadProperties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", opts)
    assert [%{status: :ok}] = result.reports
    audit = result.extraction.audit

    counter =
      Enum.find(
        audit.translated["type_decls"],
        &(&1 &&
            &1["item_meta"]["name"] == [
              %{"Ident" => ["effects_core", 0]},
              %{"Ident" => ["Counter", 0]}
            ])
      )

    assert %{"needs_drop" => false} = counter
    assert %{compiler_drop_queries: queries} = result.verification

    assert %{type_id: id, needs_drop: false} =
             Enum.find(queries, &(&1.type_id == counter["def_id"]))

    assert id == counter["def_id"]
    backend = JSON.decode!(File.read!(result.extraction.backend_llbc))
    refute Enum.any?(backend["translated"]["type_decls"], &(&1 && Map.has_key?(&1, "needs_drop")))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", opts).reports

    for value <- [nil, true, "false"] do
      altered =
        update_in(audit.translated, ["type_decls"], fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == id, do: Map.put(type, "needs_drop", value), else: type
          end)
        end)

      assert {:error, _, _} =
               Lynx.Rust.NativeDrops.audit(
                 audit.functions,
                 audit.external_calls,
                 altered,
                 audit.references
               )
    end

    missing =
      update_in(audit.translated, ["type_decls"], fn types ->
        Enum.map(types, fn type -> if type, do: Map.delete(type, "needs_drop"), else: nil end)
      end)

    assert {:error, _, _} =
             Lynx.Rust.NativeDrops.audit(
               audit.functions,
               audit.external_calls,
               missing,
               audit.references
             )

    property = Path.join(project, "Runtime/PayloadProperties.lean")
    proof = File.read!(property)

    wrong =
      String.replace(
        proof,
        "nativeRefCounter := env.nativeRefCounter + 1",
        "nativeRefCounter := env.nativeRefCounter"
      )

    refute wrong == proof
    File.write!(property, wrong)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.Project.build!(project, ["Runtime.PayloadProperties"])
    end

    File.write!(property, proof)
    Lynx.Rust.Project.build!(project, ["Runtime.PayloadProperties"])

    file = Lynx.Rust.Proofs.file!(result.extraction, ["Runtime.PayloadProperties"])
    export = Path.join(tmp, "payload.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    assert_raise CompileError,
                 ~r/native destruction requires|structural drop erasure rejected/,
                 fn ->
                   Lynx.Rust.verify!(
                     workspace,
                     "effects-native",
                     Keyword.put(opts, :roots, ["effects_native::mutex_discard_custom"])
                   )
                 end

    assert_raise CompileError, ~r/native owner lifetime|structural drop erasure rejected/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", Keyword.put(opts, :unwind, :reject))
    end

    verify_facade(workspace, project, tmp)

    core = Path.join(workspace, "core/src/lib.rs")

    File.write!(
      core,
      File.read!(core) <> "\nimpl Drop for Counter { fn drop(&mut self) { assert!(false); } }\n"
    )

    assert_raise CompileError,
                 ~r/native destruction requires|structural drop erasure rejected|assertion unwind cleanup/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "effects-native", opts)
                 end
  end

  defp verify_facade(workspace, project, tmp) do
    native_source = Path.join(workspace, "native/src/lib.rs")

    File.write!(
      native_source,
      String.replace(
        File.read!(native_source),
        "Elixir.LynxEffectsFixture.Native",
        "Elixir.LynxPayloadDropFixture.Native"
      )
    )

    options = [
      workspace: workspace,
      package: "effects-native",
      tools: @tools,
      execution: :runtime,
      unwind: :assertions,
      lean_project: project,
      build_dir: Path.join(tmp, "nif-build"),
      module_prefix: "Runtime.PayloadFacade",
      cargo: [features: ["payload-nif"]],
      only: [released_struct: 2]
    ]

    prepared = Lynx.Rustler.prepare!(options)

    assert [
             %{"name" => "released_struct", "rust_name" => "payload_release", "flags" => 1} =
               binding
           ] = prepared.bindings.bindings

    proof =
      File.read!(Path.join(@fixture, "NativePayloadRustler.lean"))
      |> String.replace("__NIF__", binding["lean_name"])

    File.write!(Path.join(project, "Runtime/PayloadFacadeProperties.lean"), proof)

    options =
      options ++
        [
          proof_modules: ["Runtime.PayloadFacadeProperties"],
          required_properties: [
            "Runtime.PayloadFacadeProperties.handler_spec",
            "Runtime.PayloadFacadeProperties.handler_prefix_spec"
          ]
        ]

    library = Path.join(tmp, "native_payload")
    File.cp!(prepared.library, library <> ".so")
    native = Path.join(tmp, "native.ex")

    File.write!(native, """
    defmodule LynxPayloadDropFixture.Native do
      @compile :debug_info
      @on_load :load_nif
      def load_nif, do: :erlang.load_nif(~c"#{library}", 0)
      def checked(_value, _amount), do: :erlang.nif_error(:not_loaded)
      def released(_value, _accepted), do: :erlang.nif_error(:not_loaded)
      def released_struct(_value, _accepted), do: :erlang.nif_error(:not_loaded)
    end
    """)

    assert {:ok, [LynxPayloadDropFixture.Native], _} =
             Kernel.ParallelCompiler.compile_to_path([native], tmp, return_diagnostics: true)

    assert apply(LynxPayloadDropFixture.Native, :released_struct, [7, true])

    assert catch_error(apply(LynxPayloadDropFixture.Native, :released_struct, [7, false])) ==
             :nif_panicked

    laws_path = Path.join(tmp, "laws.ex")

    File.write!(laws_path, ~S'''
    defmodule LynxPayloadDropFixture.Laws do
      @compile :debug_info
      use Lynx.Laws
      law cleanup_on_return,
        expects: (try do LynxPayloadDropFixture.Native.released_struct(7, true) catch :error, :nif_panicked -> false end),
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «cleanup_on_return:ensures/0»,
          Elixir.LynxPayloadDropFixture.Native.«released_struct/2»,
          Elixir.LynxPayloadDropFixture.Native.«released_struct:execution/2»,
          Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeBool, Lynx.Result.ofExcept,
          Runtime.PayloadFacadeProperties.handler_spec, Lynx.Exception.classTerm,
          Lynx.Exception.reason]
        """
      law cleanup_on_panic,
        expects: (try do LynxPayloadDropFixture.Native.released_struct(7, false); false catch :error, :nif_panicked -> true end),
        proof: ~LEAN"""
        simp [Lynx.concurrent_eq_run, «cleanup_on_panic:ensures/0»,
          Elixir.LynxPayloadDropFixture.Native.«released_struct/2»,
          Elixir.LynxPayloadDropFixture.Native.«released_struct:execution/2»,
          Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeBool, Lynx.Result.ofExcept,
          Runtime.PayloadFacadeProperties.handler_prefix_spec, Lynx.Exception.classTerm,
          Lynx.Exception.reason]
        """
    end
    ''')

    [{_, beam}] = Code.compile_file(laws_path)
    export = Path.join(tmp, "payload_nif.export")
    reports = Lynx.Laws.verify([beam], native: {Lynx.Rustler, options}, export: export)

    errors =
      for report <- reports,
          report.status != :ok,
          do: %{module: report.module, diagnostics: report.diagnostics}

    assert errors == [], inspect(errors, limit: :infinity)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output
  end
end
