module
public import RustWorkspace.DerivedFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.DerivedStruct

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
    experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.derived_struct left right =
      RustM.ok (if left ≤ right then { low := left, high := right } else { low := right, high := left }) := by
  by_cases h : left ≤ right <;>
    simp [experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.derived_struct, caller_spec, h]

theorem encoder_spec (value : experiment_nif.OrderedStruct) (env : Lynx.Rustler.Env) :
    experiment_nif.OrderedStruct.Insts.RustlerTypesEncoder.encode value env =
      RustM.ok (.map [(.atom "__struct__", .atom "Elixir.LynxOrderedFixture"),
        (.atom "low", .integer value.low.val), (.atom "high", .integer value.high.val)]) := by
  have distinct : Lynx.Rustler.Encoding.uniqueMapKeys [.atom "__struct__", .atom "low", .atom "high"] = true := by
    simp [Lynx.Rustler.Encoding.uniqueMapKeys]
  simp [experiment_nif.OrderedStruct.Insts.RustlerTypesEncoder.encode,
    experiment_nif.rustler_atoms_ordered_struct.atom_struct,
    experiment_nif.rustler_atoms_ordered_struct.atom_module,
    experiment_nif.rustler_atoms_ordered_struct.atom_low,
    experiment_nif.rustler_atoms_ordered_struct.atom_high,
    RustWorkspace.DerivedFacade.RustlerAtomCache.cache_0,
    Lynx.Rustler.Encoding.atom, Lynx.Rustler.Encoding.u64,
    Lynx.Rustler.Encoding.mapFromTermArrays, distinct, Lynx.Rustler.Encoding.unwrapOk,
    Array.to_slice, Array.make, lift]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedStruct
end RustWorkspace.DerivedStruct
