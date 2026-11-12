module
public import __PREFIX__.CoreProperties
public section
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace __PREFIX__.Properties
open __ANALYSIS__

theorem binary_tree_payload (payload : alloc.vec.Vec U8) :
    ∃ children, __ANALYSIS__.binary_tree payload = RustM.ok (.Sequence children) ∧
      children.val = [.Binary payload] :=
  singleton_payload payload

theorem binary_tree_nodes (payload : alloc.vec.Vec U8) (budget : U16) :
    __ANALYSIS__.binary_tree_nodes payload budget =
      RustM.ok (if 2 ≤ budget.val then some 2#u16 else none) := by
  obtain ⟨children, built, payloads⟩ := binary_tree_payload payload
  have size : nodes (.Sequence children) = 2 := by
    rw [nodes_sequence, payloads]
    simp
  have counted := count_owned_exact (.Sequence children) budget
  obtain ⟨result, returned, correct⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen counted)
  simp only [__ANALYSIS__.binary_tree_nodes, built, bind_ok, returned]
  cases result with
  | none => simp only [exactCount, size] at correct; rw [if_neg (by omega : ¬2 ≤ budget.val)]
  | some value =>
    simp only [exactCount, size] at correct
    have same : value = 2#u16 := by apply UScalar.eq_of_val_eq; simpa using correct.1
    simp [same, correct.2]

end __PREFIX__.Properties
