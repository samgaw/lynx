defmodule Lynx.Rust.GuardFutureTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, LLBC, NativeBorrows, NativeGuardStorage, Project, Proofs}
  @fixture Path.expand("../../fixtures/rust_effects", __DIR__)
  @tools System.get_env("LYNX_AENEAS_DIR")
  @moduletag timeout: 900_000
  @available @tools && File.regular?(Path.join(@tools, "lynx-toolchain")) &&
               String.contains?(
                 File.read!(Path.join(@tools, "lynx-toolchain")),
                 "cancelling-futures-v1"
               )
  unless @available,
    do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned cancelling-futures backend")

  @tag :tmp_dir
  test "preserves a mutated guard across real await and commits it on cancellation", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "GuardAwait"))
    property = Path.join(project, "GuardAwait/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativeGuardFuture.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::guarded_suspending"],
      futures: :cancelling,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "GuardAwait.Extraction",
      proof_modules: ["GuardAwait.Properties"],
      required_properties:
        Enum.map(
          ~w(increment_spec callee_contract initial_state drop_unstarted completed_drop first_pending_next cancel_pending_next cancel_pending first_pending suspend_then_cancel resume_contract resume_next two_polls pending_contends stale_guard_exhausts repoll_completed),
          &("GuardAwait.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports

    assert [%{type_id: guard_id, representation: :native_guard_capability}] =
             result.verification.native_guard_storage

    assert Enum.any?(
             result.verification.external_models,
             &String.starts_with?(&1, "Saved native guard capability representation")
           )

    assert Enum.any?(result.verification.guarantees, fn guarantee ->
             guarantee.kind == :cross_crate_contract &&
               guarantee.theorem == "GuardAwait.Properties.first_pending_next" &&
               "GuardAwait.Properties.callee_contract" in guarantee.contracts_used
           end)

    refute Enum.any?(result.verification.guarantees, &(&1.kind in [:nif_adapter, :elixir_law]))

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    audit = result.extraction.audit
    # The original generic guard-borrow rule remains strict; only validated
    # compiler frame inputs go through the state-sensitive lifetime audit.
    assert_raise CompileError, ~r/borrowed native guard requires nonpanicking/, fn ->
      NativeBorrows.audit!(
        audit.functions,
        audit.external_calls,
        audit.translated,
        audit.references
      )
    end

    poll =
      Enum.find(audit.functions, fn function ->
        Enum.at(function["item_meta"]["name"], 1) == %{"Ident" => ["guarded_suspending", 0]} &&
          List.last(function["item_meta"]["name"]) == %{"Ident" => ["poll", 0]}
      end)

    ordinary =
      update_in(
        poll,
        ["item_meta", "name"],
        &List.replace_at(&1, -1, %{"Ident" => ["ordinary", 0]})
      )

    assert_raise CompileError, ~r/borrowed native guard requires nonpanicking/, fn ->
      Lynx.Rust.NativeLifetimes.audit!(
        [ordinary | Enum.reject(audit.functions, &(&1 == poll))],
        audit.external_calls,
        audit.translated,
        audit.references
      )
    end

    panicking_poll = update_in(poll, ["body", "Structured", "body"], &panic_returns/1)

    assert_raise CompileError, ~r/native owner lifetime/, fn ->
      Lynx.Rust.NativeLifetimes.audit!(
        [panicking_poll | Enum.reject(audit.functions, &(&1 == poll))],
        audit.external_calls,
        audit.translated,
        audit.references
      )
    end

    raw = JSON.decode!(File.read!(result.extraction.llbc))

    assert_raise ArgumentError, ~r/saved guard requires the validated NativeGuard/, fn ->
      NativeGuardStorage.lower!(raw, audit, [], :cancelling)
    end

    backend = JSON.decode!(File.read!(result.extraction.backend_llbc))
    original_guard = Enum.find(audit.translated["type_decls"], &(&1 && &1["def_id"] == guard_id))

    backend_guard =
      Enum.find(backend["translated"]["type_decls"], &(&1 && &1["def_id"] == guard_id))

    assert %{"generics" => %{"regions" => [_]}} = original_guard

    assert %{"generics" => %{"regions" => [], "outlives" => []}, "kind" => "Opaque"} =
             backend_guard

    backend_refs = LLBC.type_references!(backend)

    increment_guard =
      Enum.find(backend["translated"]["fun_decls"], fn function ->
        function &&
          function["item_meta"]["name"] ==
            Enum.map(~w(effects_core increment_guard), &%{"Ident" => [&1, 0]})
      end)

    assert [
             %{
               "Ref" => [
                 _,
                 %{"Adt" => %{"id" => ^guard_id, "generics" => %{"regions" => []}}},
                 "Mut"
               ]
             },
             _
           ] =
             CallModels.expand(increment_guard["signature"]["inputs"], backend_refs)

    file =
      Proofs.file!(result.extraction, ["GuardAwait.Properties"],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "guard-await.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom nativeTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, ["GuardAwait.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    incorrect =
      String.replace(
        original,
        "(.ok (), released env updated poisoned)",
        "(.ok (), released env value poisoned)",
        global: false
      )

    refute incorrect == original
    File.write!(property, incorrect)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["GuardAwait.Properties"])
    end

    File.write!(property, original)

    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)

    changed =
      String.replace(
        source,
        "let changed = effects_core::increment_guard(&mut guard, amount);",
        "let changed = effects_core::increment_guard(&mut guard, 0);",
        global: false
      )

    refute changed == source
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(native, source)
    core = Path.join(workspace, "core/src/lib.rs")
    core_source = File.read!(core)

    changed_core =
      String.replace(
        core_source,
        "counter.value.checked_add(amount)",
        "counter.value.checked_add(0)",
        global: false
      )

    refute changed_core == core_source
    File.write!(core, changed_core)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(core, core_source)

    panicking =
      String.replace(
        source,
        "let changed = effects_core::increment_guard(&mut guard, amount);",
        "let changed = effects_core::increment_guard(&mut guard, amount);\n    assert!(changed);",
        global: false
      )

    refute panicking == source
    File.write!(native, panicking)

    assert_raise CompileError,
                 ~r/native owner lifetime|borrowed native guard|unwind|native drop/,
                 fn ->
                   Lynx.Rust.verify!(workspace, "effects-native", options)
                 end

    File.write!(native, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end

  defp panic_returns(%{"kind" => "Return"} = statement),
    do: Map.put(statement, "kind", %{"Panic" => %{"on_unwind" => %{"statements" => []}}})

  defp panic_returns(map) when is_map(map),
    do: Map.new(map, fn {key, value} -> {key, panic_returns(value)} end)

  defp panic_returns(list) when is_list(list), do: Enum.map(list, &panic_returns/1)
  defp panic_returns(value), do: value
end
