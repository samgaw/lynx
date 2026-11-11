defmodule Lynx.Rust.ResultModelsTest do
  use ExUnit.Case
  alias Lynx.Rust.LLBC

  @tools System.get_env("LYNX_AENEAS_DIR")
  @fixture Path.expand("../../fixtures/rust_workspace", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "map_err composes actual cross-crate and callback implementations, retaining panic semantics",
       %{
         tmp_dir: tmp
       } do
    workspace = Path.join(tmp, "workspace")

    for crate <- ["base", "analysis"], do: File.mkdir_p!(Path.join([workspace, crate, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "map-base"
    version = "0.1.0"
    edition = "2021"
    """)

    File.write!(Path.join(workspace, "base/src/lib.rs"), """
    pub fn choose(value: bool) -> Result<bool, bool> {
        if value { Ok(value) } else { Err(value) }
    }
    pub fn stamp(input: Result<u64, u64>, mask: u64) -> Result<u64, u64> {
        input.map_err(move |error| error ^ mask)
    }
    """)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "map-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    map-base = { path = "../base" }
    """)

    source = Path.join(workspace, "analysis/src/lib.rs")

    original = """
    pub fn stamp_result(input: Result<u64, u64>, mask: u64) -> Result<u64, u64> {
        map_base::stamp(input, mask)
    }
    pub fn captured_panic(input: Result<bool, bool>, fail: bool) -> Result<bool, bool> {
        input.map_err(move |error| { assert!(!fail); error })
    }
    pub fn map_error(value: bool) -> Result<bool, bool> {
        map_base::choose(value).map_err(|error| !error)
    }
    pub fn map_error_borrowed<'env>(_marker: &'env bool, value: bool) -> Result<bool, bool> {
        map_base::choose(value).map_err(|error| !error)
    }
    pub fn promoted_threshold<'env>(_marker: &'env bool) -> &'env usize {
        &(1 + 1)
    }
    pub fn panic_error(value: bool) -> Result<bool, bool> {
        map_base::choose(value).map_err(|_| panic!())
    }
    """

    File.write!(source, original)

    {output, status} =
      System.cmd(
        "cargo",
        ["generate-lockfile", "--manifest-path", Path.join(workspace, "Cargo.toml")],
        stderr_to_stdout: true
      )

    assert status == 0, output
    project = Path.join(tmp, "proofs")
    File.mkdir_p!(Path.join(project, "ResultModels"))
    packages = Path.join(@fixture, "proofs/.lake/packages")

    if File.dir?(packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "ResultModels/Properties.lean"), """
    module
    public import ResultModels.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace ResultModels.Properties
    theorem choose_spec (value : Bool) :
        map_analysis.map_base.choose value = RustM.ok (if value then .Ok value else .Err value) := by
      cases value <;> rfl
    theorem error_callback_spec (value : Bool) :
        map_analysis.map_error.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool.call_once () value =
          RustM.ok (!value) := by rfl
    theorem panic_callback_spec (value : Bool) :
        map_analysis.panic_error.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool.call_once () value =
          RustM.fail .panic := by rfl
    theorem map_error_spec (value : Bool) :
        map_analysis.map_error value = RustM.ok (if value then .Ok value else .Err (!value)) := by
      cases value <;> simp [map_analysis.map_error, choose_spec, core.result.Result.map_err,
        map_analysis.map_error.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool, error_callback_spec]
    theorem borrowed_callback (marker value : Bool) :
        map_analysis.map_error_borrowed marker value = RustM.ok (if value then .Ok value else .Err (!value)) := by
      cases value <;> simp [map_analysis.map_error_borrowed, choose_spec, core.result.Result.map_err,
        map_analysis.map_error_borrowed.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool,
        map_analysis.map_error_borrowed.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool.call_once]
    theorem promoted_scalar (marker : Bool) :
        map_analysis.promoted_threshold marker = RustM.ok 2#usize := by
      have spec := Usize.add_bv_spec (x := 1#usize) (y := 1#usize) (by scalar_tac)
      obtain ⟨value, returned, property⟩ := triple_iff_exists_ok.mp (WP.spec_to_mvcgen spec)
      have valueTwo : value = 2#usize := (UScalar.eq_equiv _ _).mpr (by simpa using property.1)
      have wrapped : (1#usize).wrapping_add 1#usize = value :=
        (UScalar.eq_equiv_bv_eq _ _).mpr (by simpa using property.2.symm)
      simp [map_analysis.promoted_threshold, returned, Usize.wrapping_add, wrapped, valueTwo]
    theorem callback_not_run_on_ok : map_analysis.panic_error true = RustM.ok (.Ok true) := by
      simp [map_analysis.panic_error, choose_spec, core.result.Result.map_err,
        map_analysis.panic_error.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool, panic_callback_spec]
    theorem callback_panic_on_err : map_analysis.panic_error false = RustM.fail .panic := by
      simp [map_analysis.panic_error, choose_spec, core.result.Result.map_err,
        map_analysis.panic_error.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool, panic_callback_spec]
    theorem stamp_core (input : core.result.Result U64 U64) (mask : U64) :
        map_analysis.map_base.stamp input mask = RustM.ok
          (match input with | .Ok value => .Ok value | .Err error => .Err (error ^^^ mask)) := by
      cases input <;> simp [map_analysis.map_base.stamp, core.result.Result.map_err,
        map_analysis.map_base.stamp.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once]
    theorem stamp_composed (input : core.result.Result U64 U64) (mask : U64) :
        map_analysis.stamp_result input mask = RustM.ok
          (match input with | .Ok value => .Ok value | .Err error => .Err (error ^^^ mask)) := by
      simp [map_analysis.stamp_result, stamp_core]
    theorem skipped_capture (value fail : Bool) :
        map_analysis.captured_panic (.Ok value) fail = RustM.ok (.Ok value) := by
      simp [map_analysis.captured_panic, core.result.Result.map_err]
    theorem captured_panics (value : Bool) :
        map_analysis.captured_panic (.Err value) true = RustM.fail .panic := by
      simp [map_analysis.captured_panic, core.result.Result.map_err,
        map_analysis.captured_panic.closure.Insts.CoreOpsFunctionFnOnceTupleBoolBool.call_once]
    end ResultModels.Properties
    """)

    options = [
      roots: [
        "map_analysis::map_error",
        "map_analysis::panic_error",
        "map_analysis::map_error_borrowed",
        "map_analysis::promoted_threshold",
        "map_analysis::stamp_result",
        "map_analysis::captured_panic"
      ],
      lean_project: project,
      module_prefix: "ResultModels.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["ResultModels.Properties"],
      required_properties: [
        "ResultModels.Properties.map_error_spec",
        "ResultModels.Properties.borrowed_callback",
        "ResultModels.Properties.promoted_scalar",
        "ResultModels.Properties.callback_not_run_on_ok",
        "ResultModels.Properties.callback_panic_on_err",
        "ResultModels.Properties.stamp_core",
        "ResultModels.Properties.stamp_composed",
        "ResultModels.Properties.skipped_capture",
        "ResultModels.Properties.captured_panics"
      ]
    ]

    result = Lynx.Rust.verify!(workspace, "map-analysis", options)

    assert [
             %{
               rust_name: "core::result::{core::result::Result<@T, @E>}::map_err",
               implementation_verified: false,
               status: :modelled
             }
           ] = result.verification.unverified_external_calls

    assert Enum.any?(result.verification.guarantees, fn row ->
             row.kind == :cross_crate_contract and
               row.theorem == "ResultModels.Properties.map_error_spec" and
               "ResultModels.Properties.choose_spec" in row.contracts_used
           end)

    root =
      Enum.find_value(result.extraction.implementations, fn
        {id, %{"rust_name" => "map_analysis::map_error"}} -> id
        _ -> nil
      end)

    [callback] = result.extraction.audit.callback_dependencies[root]
    assert callback in LLBC.dependencies(result.extraction.audit)[root]

    export = Path.join(tmp, "map-error.export")
    file = Lynx.Rust.Proofs.file!(result.extraction, ["ResultModels.Properties"])
    assert [%{status: :ok}] = Lynx.Commands.verify!(project, [file], export: export)
    sandbox = if :os.type() == {:unix, :darwin}, do: ["--inadvisably-no-sandbox"], else: []
    {status, output} = Lynx.Commands.lake(project, ["check", "--from-export", export] ++ sandbox)
    assert status == 0, output

    document = JSON.decode!(File.read!(result.extraction.llbc))
    assert_callback_rejections(document, result.extraction.audit, root, callback)

    # The same theorem must fail after changing the actual callback implementation.
    File.write!(source, String.replace(original, "|error| !error", "|error| error"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "map-analysis", options)
    end

    # The original theorem must also reject a different scalar-capturing callback.
    File.write!(
      source,
      String.replace(
        original,
        "map_base::choose(value).map_err(|error| !error)",
        "let captured = value;\n    map_base::choose(value).map_err(move |error| error || captured)"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "map-analysis", options)
    end
  end

  defp assert_callback_rejections(document, audit, root, callback) do
    [model_id] = Map.keys(audit.external_calls)
    model = audit.external_calls[model_id]

    closure =
      Enum.find(audit.translated["type_decls"], fn type ->
        case type do
          %{"src" => %{"Closure" => %{"info" => %{"closure_body" => %{"id" => id}}}}} ->
            id == callback

          _ ->
            false
        end
      end)

    impl = get_in(closure, ["src", "Closure", "info", "fn_once_impl", "skip_binder", "id"])
    boolean = %{"Scalar" => "Bool"}

    mutations = [
      change(document, "fun_decls", model_id, &put_in(&1, ["signature", "abi"], "C")),
      change(
        document,
        "fun_decls",
        model_id,
        &put_in(&1, ["signature", "inputs"], Enum.reverse(&1["signature"]["inputs"]))
      ),
      change(
        document,
        "fun_decls",
        callback,
        &put_in(&1, ["generics", "types"], [%{"index" => 0}])
      ),
      change(document, "fun_decls", callback, &put_in(&1, ["signature", "is_unsafe"], true)),
      change(document, "fun_decls", model_id, &put_in(&1, ["generics", "types"], [])),
      change(
        document,
        "trait_decls",
        model.fn_once_trait,
        &put_in(&1, ["item_meta", "name"], [%{"Ident" => ["other", 0]}])
      ),
      change(
        document,
        "trait_decls",
        model.destruct_trait,
        &put_in(&1, ["item_meta", "name"], [%{"Ident" => ["other", 0]}])
      ),
      change(
        document,
        "type_decls",
        closure["def_id"],
        &put_in(&1, ["kind", "Struct"], [%{"ty" => %{"Ref" => ["Static", boolean, "Shared"]}}])
      ),
      change(document, "type_decls", closure["def_id"], &put_in(&1, ["src"], "Normal")),
      change(
        document,
        "type_decls",
        closure["def_id"],
        &put_in(&1, ["src", "Closure", "info", "closure_body", "id"], root)
      ),
      change(document, "fun_decls", callback, &put_in(&1, ["signature", "abi"], "C")),
      change(
        document,
        "fun_decls",
        callback,
        &put_in(&1, ["signature", "output"], %{"Scalar" => %{"Integer" => %{"Unsigned" => "U64"}}})
      ),
      change(document, "fun_decls", callback, &put_in(&1, ["body"], "Opaque")),
      change(
        document,
        "fun_decls",
        root,
        &put_in(&1, ["signature", "abi"], %{"Other" => "rust-call"})
      ),
      change(
        document,
        "trait_impls",
        impl,
        &put_in(&1, ["methods", Access.at(0), "skip_binder", "id"], root)
      ),
      change(document, "trait_impls", impl, &put_in(&1, ["is_negative"], true)),
      rewrite(document, fn
        %{"BuiltinOrAuto" => %{"builtin_data" => "NoopDestruct"} = data} = node ->
          %{node | "BuiltinOrAuto" => %{data | "builtin_data" => "OtherDestruct"}}

        node ->
          node
      end)
    ]

    for invalid <- mutations do
      assert_raise CompileError, fn -> LLBC.audit!(invalid, ["map_analysis", "map_base"]) end
    end

    missing =
      update_in(
        document,
        ["translated", "fun_decls"],
        &Enum.reject(&1, fn item -> item && item["def_id"] == callback end)
      )

    assert_raise CompileError, ~r/extracted compiler FnOnce/, fn ->
      LLBC.audit!(missing, ["map_analysis", "map_base"])
    end
  end

  defp change(document, kind, id, fun) do
    update_in(
      document,
      ["translated", kind],
      &Enum.map(&1, fn
        %{"def_id" => ^id} = item -> fun.(item)
        item -> item
      end)
    )
  end

  defp rewrite(value, fun) when is_map(value),
    do: value |> Map.new(fn {k, v} -> {k, rewrite(v, fun)} end) |> fun.()

  defp rewrite(values, fun) when is_list(values), do: Enum.map(values, &rewrite(&1, fun))
  defp rewrite(value, _), do: value
end
