defmodule Lynx.Rust.OptionCallbacksTest do
  use ExUnit.Case

  @tools System.get_env("LYNX_AENEAS_DIR")
  @packages Path.expand("../../fixtures/rust_workspace/proofs/.lake/packages", __DIR__)
  @moduletag timeout: 600_000
  if is_nil(@tools), do: @moduletag(skip: "set LYNX_AENEAS_DIR to the pinned Aeneas distribution")

  @tag :tmp_dir
  test "Option callbacks compose actual implementations and preserve skipped panics", %{
    tmp_dir: tmp
  } do
    workspace = Path.join(tmp, "workspace")
    for crate <- ~w(base analysis), do: File.mkdir_p!(Path.join([workspace, crate, "src"]))

    File.write!(Path.join(workspace, "Cargo.toml"), """
    [workspace]
    members = ["base", "analysis"]
    resolver = "2"
    """)

    File.write!(Path.join(workspace, "base/Cargo.toml"), """
    [package]
    name = "option-base"
    version = "0.1.0"
    edition = "2021"
    """)

    base_source = Path.join(workspace, "base/src/lib.rs")

    base_original = """
    pub fn choose(value: bool) -> Option<bool> {
        if value { Some(value) } else { None }
    }
    pub fn bounded(input: Option<usize>, bytes: &[u8]) -> Option<usize> {
        input.and_then(|length| {
            if length <= bytes.len() {
                Some(length)
            } else {
                None
            }
        })
    }
    """

    File.write!(base_source, base_original)

    File.write!(Path.join(workspace, "analysis/Cargo.toml"), """
    [package]
    name = "option-analysis"
    version = "0.1.0"
    edition = "2021"
    [dependencies]
    option-base = { path = "../base" }
    """)

    source = Path.join(workspace, "analysis/src/lib.rs")

    original = """
    pub fn bounded_length(input: Option<usize>, bytes: &[u8]) -> Option<usize> {
        option_base::bounded(input, bytes)
    }
    pub fn captured(input: Option<u64>, mask: u64) -> Option<u64> {
        input.and_then(move |value| Some(value ^ mask))
    }
    pub fn invert(value: bool) -> Option<bool> {
        option_base::choose(value).and_then(|value| if value { Some(!value) } else { None })
    }
    pub fn borrowed(value: Option<&&bool>) -> Option<bool> {
        value.and_then(|value| if **value { Some(false) } else { None })
    }
    pub fn panic_some(value: bool) -> Option<bool> {
        option_base::choose(value).and_then(|_| panic!())
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
    File.mkdir_p!(Path.join(project, "OptionProofs"))

    if File.dir?(@packages) do
      File.mkdir_p!(Path.join(project, ".lake"))
      File.ln_s!(@packages, Path.join(project, ".lake/packages"))
    end

    File.write!(Path.join(project, "OptionProofs/Properties.lean"), """
    module
    public import OptionProofs.Extraction.Funs
    public section
    open Aeneas Aeneas.Std
    namespace OptionProofs.Properties
    theorem compose (value : Bool) :
        option_analysis.invert value = RustM.ok (if value then some false else none) := by
      cases value <;> simp [option_analysis.invert, option_analysis.option_base.choose,
        OptionProofs.Extraction.Option.andThen,
        option_analysis.invert.closure.Insts.CoreOpsFunctionFnOnceTupleBoolOptionBool,
        option_analysis.invert.closure.Insts.CoreOpsFunctionFnOnceTupleBoolOptionBool.call_once]
    theorem borrowed (value : Option Bool) :
        option_analysis.borrowed value = RustM.ok (value.bind fun bit => if bit then some false else none) := by
      cases value with
      | none => simp [option_analysis.borrowed, OptionProofs.Extraction.Option.andThen]
      | some value =>
        cases value <;> simp [option_analysis.borrowed, OptionProofs.Extraction.Option.andThen,
          option_analysis.borrowed.closure.Insts.CoreOpsFunctionFnOnceTupleShared0Shared1BoolOptionBool,
          option_analysis.borrowed.closure.Insts.CoreOpsFunctionFnOnceTupleShared0Shared1BoolOptionBool.call_once]
    theorem skipped : option_analysis.panic_some false = RustM.ok none := by
      simp [option_analysis.panic_some, option_analysis.option_base.choose,
        OptionProofs.Extraction.Option.andThen]
    theorem panics : option_analysis.panic_some true = RustM.fail .panic := by
      simp [option_analysis.panic_some, option_analysis.option_base.choose,
        OptionProofs.Extraction.Option.andThen,
        option_analysis.panic_some.closure.Insts.CoreOpsFunctionFnOnceTupleBoolOptionBool,
        option_analysis.panic_some.closure.Insts.CoreOpsFunctionFnOnceTupleBoolOptionBool.call_once]
    theorem captured (input : Option U64) (mask : U64) :
        option_analysis.captured input mask = RustM.ok (input.map fun value => value ^^^ mask) := by
      cases input <;> simp [option_analysis.captured, OptionProofs.Extraction.Option.andThen,
        option_analysis.captured.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once,
        Aeneas.Std.lift]
    theorem bounded_core (input : Option Usize) (bytes : Slice U8) :
        option_analysis.option_base.bounded input bytes = RustM.ok
          (match input with
          | none => none
          | some length => if length.val ≤ bytes.val.length then some length else none) := by
      cases input with
      | none => simp [option_analysis.option_base.bounded, OptionProofs.Extraction.Option.andThen]
      | some length =>
        by_cases h : length.val ≤ bytes.val.length <;>
          simp [option_analysis.option_base.bounded, OptionProofs.Extraction.Option.andThen,
            option_analysis.option_base.bounded.closure.Insts.CoreOpsFunctionFnOnceTupleUsizeOptionUsize.call_once,
            h, UScalar.le_equiv, Slice.len_val]
    theorem bounded_composed (input : Option Usize) (bytes : Slice U8) :
        option_analysis.bounded_length input bytes = RustM.ok
          (match input with
          | none => none
          | some length => if length.val ≤ bytes.val.length then some length else none) := by
      simp [option_analysis.bounded_length, bounded_core]
    end OptionProofs.Properties
    """)

    options = [
      roots: [
        "option_analysis::bounded_length",
        "option_analysis::captured",
        "option_analysis::invert",
        "option_analysis::panic_some",
        "option_analysis::borrowed"
      ],
      lean_project: project,
      module_prefix: "OptionProofs.Extraction",
      build_dir: Path.join(tmp, "build"),
      proof_modules: ["OptionProofs.Properties"],
      required_properties:
        Enum.map(
          ~w(compose borrowed skipped panics captured bounded_core bounded_composed),
          &("OptionProofs.Properties." <> &1)
        )
    ]

    result = Lynx.Rust.verify!(workspace, "option-analysis", options)

    assert [
             %{
               rust_name: "core::option::{core::option::Option<@T>}::and_then",
               implementation_verified: false,
               status: :modelled
             },
             %{
               rust_name: "core::slice::{[@T]}::len",
               implementation_verified: false,
               status: :modelled
             }
           ] = result.verification.unverified_external_calls

    assert Enum.any?(result.extraction.audit.callback_dependencies, fn {_, ids} ->
             length(ids) == 1
           end)

    assert "OptionProofs.Extraction.OptionModel" in result.extraction.audit_modules

    document = JSON.decode!(File.read!(result.extraction.llbc))
    model = result.extraction.audit.external_calls |> Map.values() |> hd()

    for changed <- [
          put_in(model.function, ["signature", "abi"], "C"),
          put_in(model.function, ["signature", "output"], %{"Scalar" => "Bool"}),
          put_in(model.function, ["generics", "trait_clauses"], [])
        ] do
      assert Lynx.Rust.ResultModels.resolve(
               changed,
               result.extraction.audit.translated,
               result.extraction.audit.references
             ) == nil
    end

    borrowed =
      Enum.find_value(result.extraction.implementations, fn
        {id, %{"rust_name" => "option_analysis::borrowed"}} -> id
        _ -> nil
      end)

    [callback] = result.extraction.audit.callback_dependencies[borrowed]

    method =
      Enum.find(
        result.extraction.audit.translated["fun_decls"],
        &(&1 && &1["def_id"] == callback)
      )

    assert method["generics"]["outlives"] != []
    impl = get_in(method, ["src", "TraitImpl", "impl_ref", "id"])

    for bad <- [
          [%{"Var" => %{"Free" => 99}}, %{"Var" => %{"Free" => 0}}],
          [%{"Lub" => %{"Scalar" => "Bool"}}, %{"Var" => %{"Free" => 0}}],
          [%{"Var" => %{"Bound" => [0, 0]}}, %{"Var" => %{"Free" => 0}}]
        ] do
      invalid =
        Enum.reduce([{"fun_decls", callback}, {"trait_impls", impl}], document, fn {kind, id},
                                                                                   doc ->
          update_in(doc, ["translated", kind], fn rows ->
            Enum.map(rows, fn
              %{"def_id" => ^id} = row ->
                put_in(row, ["generics", "outlives"], [
                  %{"regions" => [], "outlives" => [], "skip_binder" => bad}
                ])

              row ->
                row
            end)
          end)
        end)

      assert_raise CompileError, ~r/extracted compiler FnOnce/, fn ->
        Lynx.Rust.LLBC.audit!(invalid, ["option_analysis", "option_base"])
      end
    end

    File.write!(
      base_source,
      String.replace(base_original, "length <= bytes.len()", "length < bytes.len()")
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "option-analysis", options)
    end

    File.write!(base_source, base_original)

    File.write!(source, String.replace(original, "Some(!value)", "Some(value)"))

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "option-analysis", options)
    end

    File.write!(
      source,
      String.replace(
        original,
        "|value| if value { Some(!value) } else { None }",
        "|inner| if inner { Some(inner == value) } else { None }"
      )
    )

    assert_raise RuntimeError, ~r/native Lean project command failed/, fn ->
      Lynx.Rust.verify!(workspace, "option-analysis", options)
    end
  end
end
