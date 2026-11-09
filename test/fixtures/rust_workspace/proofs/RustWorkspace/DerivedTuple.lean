module
public import RustWorkspace.DerivedFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.DerivedTuple

theorem core_spec (left right : U64) :
    experiment_nif.experiment_core.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := by
  unfold experiment_nif.experiment_core.order_pair
  split <;> rfl

theorem caller_spec (left right : U64) :
    experiment_nif.experiment_analysis.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := core_spec left right

theorem ordered_fields (left right : U64) :
    ∃ low high, experiment_nif.experiment_analysis.order_pair left right = RustM.ok (low, high) ∧
      low.val ≤ high.val ∧ ((low = left ∧ high = right) ∨ (low = right ∧ high = left)) := by
  by_cases h : left ≤ right
  · refine ⟨left, right, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · simp [caller_spec, h]
    · exact h
  · refine ⟨right, left, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
    · simp [caller_spec, h]
    · change ¬ left.val ≤ right.val at h
      omega

theorem facade_spec (left right : U64) :
    experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.derived_pair left right =
      RustM.ok (if left ≤ right then { low := left, high := right } else { low := right, high := left }) := by
  by_cases h : left ≤ right <;>
    simp [experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.derived_pair, caller_spec, h]

theorem encoder_spec (value : experiment_nif.OrderedFields) (env : Lynx.Rustler.Env) :
    experiment_nif.OrderedFields.Insts.RustlerTypesEncoder.encode value env =
      RustM.ok (.tuple #[.integer value.low.val, .integer value.high.val]) := by
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesEncoder.encode,
    Lynx.Rustler.Encoding.u64, Lynx.Rustler.Encoding.makeTuple,
    Array.to_slice, Array.make, lift]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedTuple
end RustWorkspace.DerivedTuple
