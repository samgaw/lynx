module
public import RustWorkspace.DerivedFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.DerivedList

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

@[expose] def pairValues (left right : U64) : alloc.vec.Vec U64 :=
  alloc.vec.Vec.from [left, right] (by simp; scalar_tac)

theorem facade_spec (left right : U64) :
    experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.derived_list left right =
      RustM.ok (if left ≤ right then ⟨pairValues left right⟩ else ⟨pairValues right left⟩) := by
  by_cases h : left ≤ right <;>
    simp [experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.derived_list,
      caller_spec, h, RustWorkspace.DerivedFacade.VectorModel.push_eq,
      alloc.vec.Vec.new, pairValues]

theorem encoder_spec (value : experiment_nif.OrderedList) (env : Lynx.Rustler.Env)
    (bound : value.values.val.length ≤ 2147483647) :
    experiment_nif.OrderedList.Insts.RustlerTypesEncoder.encode value env =
      RustM.ok (.tuple #[Lynx.Term.list (value.values.val.map (fun n => .integer n.val))]) := by
  have elements : List.Forall₂ (fun n term =>
      experiment_nif.U64.Insts.RustlerTypesEncoder.encode n env = RustM.ok term)
      value.values.val (value.values.val.map (fun n => .integer n.val)) := by
    induction value.values.val with
    | nil => exact .nil
    | cons head tail ih => exact .cons rfl ih
  have encoded := Lynx.Rustler.Encoding.vec_values
    experiment_nif.U64.Insts.RustlerTypesEncoder value.values env _ bound elements
  simp [experiment_nif.OrderedList.Insts.RustlerTypesEncoder.encode, encoded,
    Lynx.Rustler.Encoding.makeTuple, Array.to_slice, Array.make, lift]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedList

end RustWorkspace.DerivedList
