module
public import __PREFIX__.DriverProperties
public section
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace __PREFIX__.Properties
open __ANALYSIS__

theorem inspect_exact (node : __CORE__.Node) (budget : U16) :
    Aeneas.Std.WP.spec (__ANALYSIS__.tree_nodes node budget) (exactCount (nodes node) budget) :=
  count_exact node budget

theorem inspect_fits (node : __CORE__.Node) (budget : U16)
    (fits : nodes node ≤ budget.val) :
    ∃ used, __ANALYSIS__.tree_nodes node budget = RustM.ok (some used) ∧ used.val = nodes node := by
  obtain ⟨result, returned, correct⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (inspect_exact node budget))
  cases result with
  | none => simp only [exactCount] at correct; omega
  | some used => exact ⟨used, returned, correct.1⟩

theorem inspect_rejects (node : __CORE__.Node) (budget : U16)
    (insufficient : budget.val < nodes node) :
    __ANALYSIS__.tree_nodes node budget = RustM.ok none := by
  obtain ⟨result, returned, correct⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (inspect_exact node budget))
  cases result with
  | none => exact returned
  | some used => simp only [exactCount] at correct; omega

theorem constructed_count (payload : alloc.vec.Vec U8) :
    ∃ tree, __ANALYSIS__.binary_tree payload = RustM.ok tree ∧
      __ANALYSIS__.tree_nodes tree 2#u16 = RustM.ok (some 2#u16) ∧
      __ANALYSIS__.tree_nodes tree 1#u16 = RustM.ok none := by
  obtain ⟨children, built, payloads⟩ := binary_tree_payload payload
  have size : nodes (.Sequence children) = 2 := by
    rw [nodes_sequence, payloads]
    simp
  obtain ⟨used, counted, exactSize⟩ := inspect_fits (.Sequence children) 2#u16 (by rw [size]; simp)
  have same : used = 2#u16 := by apply UScalar.eq_of_val_eq; simpa [size] using exactSize
  refine ⟨.Sequence children, built, ?_, ?_⟩
  · simpa [same] using counted
  · exact inspect_rejects _ _ (by rw [size]; simp)

end __PREFIX__.Properties
