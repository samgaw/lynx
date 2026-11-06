defmodule Lynx.Rust.CancellingFutureTest do
  use ExUnit.Case
  alias Lynx.Rust.{CallModels, LLBC, Project, Proofs}
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
  test "proves compiler cancellation and completion reclaim a mutex retained across await", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    File.mkdir_p!(workspace)

    for path <- ~w(Cargo.toml Cargo.lock core native),
        do: File.cp_r!(Path.join(@fixture, path), Path.join(workspace, path))

    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "Cancel"))
    property = Path.join(project, "Cancel/Properties.lean")
    original = File.read!(Path.join(@fixture, "NativeCancellingFuture.lean"))
    File.write!(property, original)
    packages = Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    options = [
      roots: ["effects_native::owned_suspending"],
      futures: :cancelling,
      execution: :runtime,
      tools: @tools,
      lean_project: project,
      build_dir: Path.join(tmp, "build"),
      module_prefix: "Cancel.Extraction",
      proof_modules: ["Cancel.Properties"],
      required_properties:
        Enum.map(
          ~w(internal_initial_state core_increment callee_pending callee_ready initial_state drop_unstarted drop_invalid_tag drop_missing_owner first_pending_next first_pending cancel_pending completed_drop suspend_then_cancel resume_ready),
          &("Cancel.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "effects-native", options)
    assert [%{status: :ok}] = result.reports
    assert result.verification.futures == :cancelling

    assert Enum.any?(
             result.verification.implementations,
             &String.ends_with?(&1.lean_name, "owned_suspending.closure.drop_owned")
           )

    assert Enum.any?(
             result.verification.external_models,
             &String.contains?(&1, "actual rustc drop MIR")
           )

    assert [%{status: :ok, cached: true}] =
             Lynx.Rust.verify!(workspace, "effects-native", options).reports

    translated = result.extraction.audit.translated

    coroutine =
      Enum.find(translated["type_decls"], fn type ->
        type && List.last(type["item_meta"]["name"]) == %{"Builtin" => ["Closure", 0]}
      end)

    attributes = coroutine["item_meta"]["attr_info"]["attributes"]

    evidence =
      Enum.find(
        attributes,
        &match?(%{"Unknown" => %{"path" => "lynx::coroutine_storage_v1"}}, &1)
      )

    for invalid <- [
          attributes ++ [evidence],
          Enum.map(attributes, fn attribute ->
            if attribute == evidence,
              do:
                put_in(
                  attribute,
                  ["Unknown", "args"],
                  JSON.encode!(%{"state" => 999, "states" => [[], [], []]})
                ),
              else: attribute
          end)
        ] do
      altered =
        update_in(translated, ["type_decls"], fn types ->
          Enum.map(types, fn type ->
            if type && type["def_id"] == coroutine["def_id"],
              do: put_in(type, ["item_meta", "attr_info", "attributes"], invalid),
              else: type
          end)
        end)

      audit = result.extraction.audit

      assert_raise CompileError, ~r/compiler coroutine/, fn ->
        Lynx.Rust.NativeLifetimes.audit!(
          audit.functions,
          audit.external_calls,
          altered,
          audit.references
        )
      end
    end

    replace =
      Enum.find(translated["fun_decls"], fn function ->
        function &&
          function["item_meta"]["name"] == Enum.map(~w(core mem replace), &%{"Ident" => [&1, 0]})
      end)

    refs = LLBC.type_references!(%{"translated" => translated})

    assert %{builtin: true, native_replace: true} =
             CallModels.resolve([replace], translated, refs, [], :runtime)[replace["def_id"]]

    refute CallModels.resolve(
             [put_in(replace, ["signature", "is_unsafe"], true)],
             translated,
             refs,
             [],
             :runtime
           )[replace["def_id"]]

    file =
      Proofs.file!(result.extraction, ["Cancel.Properties"],
        required_properties: options[:required_properties]
      )

    export = Path.join(tmp, "cancel.export")
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    for extra <- [
          "private axiom nativeTrust : False",
          "private theorem unfinished : True := by sorry"
        ] do
      File.write!(property, original <> "\n" <> extra <> "\n")
      Project.build!(project, ["Cancel.Properties"])
      assert [%{status: :error}] = Lynx.Commands.verify!(project, [file])
    end

    false_property =
      String.replace(original, "(.ok (), reclaimed env)", "(.ok (), retained env value)")

    refute false_property == original
    File.write!(property, false_property)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Project.build!(project, ["Cancel.Properties"])
    end

    File.write!(property, original)

    native = Path.join(workspace, "native/src/lib.rs")
    source = File.read!(native)

    changed =
      String.replace(
        source,
        "let mutex = Mutex::new(value);\n    let result = effects_core::paused_counter(value).await;",
        "let mutex = Mutex::new(value.saturating_add(1));\n    let result = effects_core::paused_counter(value).await;"
      )

    refute changed == source
    File.write!(native, changed)

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "effects-native", options)
    end

    File.write!(native, source)
    assert [%{status: :ok}] = Lynx.Rust.verify!(workspace, "effects-native", options).reports
  end
end
