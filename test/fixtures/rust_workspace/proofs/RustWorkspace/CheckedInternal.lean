module
public import RustWorkspace.CheckedInternalExtraction.Funs
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std experiment_analysis
namespace RustWorkspace.CheckedInternal

theorem core_spec (value : I64) :
    experiment_analysis.experiment_core.evaluate value = RustM.ok (I64.checked_mul value 2#i64) := rfl

theorem caller_spec (value : I64) :
    analyse value = RustM.ok (match I64.checked_mul value 2#i64 with
      | none => none
      | some product => I64.checked_add product 1#i64) := by
  simp only [analyse, core_spec, bind_ok]
  cases I64.checked_mul value 2#i64 <;> simp [Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]

theorem output_spec (value : I64) :
    ∃ result, analyse value = RustM.ok result ∧
      match result with
      | none => ¬ (-4611686018427387904 ≤ value.val ∧ value.val < 4611686018427387904)
      | some output => -4611686018427387904 ≤ value.val ∧ value.val < 4611686018427387904 ∧
          output.val = 2 * value.val + 1 := by
  have mul_spec := Lynx.Rust.Scalar.checkedMulI64_spec value 2#i64
  have one : (1#i64).val = 1 := by decide
  have two : (2#i64).val = 2 := by decide
  cases multiplied : I64.checked_mul value 2#i64 with
  | none =>
    refine ⟨none, by simp [caller_spec, multiplied], ?_⟩
    simp only [multiplied, I64.min_eq, I64.max_eq, two] at mul_spec
    omega
  | some product =>
    simp only [multiplied, I64.min_eq, I64.max_eq, two] at mul_spec
    have add_spec := Lynx.Rust.Scalar.checkedAddI64_spec product 1#i64
    cases added : I64.checked_add product 1#i64 with
    | none =>
      simp only [added, I64.min_eq, I64.max_eq, one] at add_spec
      omega
    | some output =>
      refine ⟨some output, by simp [caller_spec, multiplied, added], ?_⟩
      simp only [added, I64.min_eq, I64.max_eq, one] at add_spec
      omega

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.CheckedInternalExtraction.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.NativeTry
  LynxTest.ProofAudit.checkModule `RustWorkspace.CheckedInternal

end RustWorkspace.CheckedInternal
