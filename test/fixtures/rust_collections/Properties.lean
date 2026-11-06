module
public import Collections.Extraction.Funs
public section
open Aeneas Aeneas.Std experiment_analysis
namespace Collections.Properties

theorem slice_transition (input : Slice U8) (value : U8) :
    experiment_core.collections.replace_slice_first input value =
      RustM.ok (!input.val.isEmpty, input.set 0#usize value) := by
  cases shape : input.val with
  | nil =>
    have unchanged : input.set 0#usize value = input := by
      apply Slice.ext
      simp [Slice.set_val_eq, shape]
    simp [experiment_core.collections.replace_slice_first, core.slice.Slice.is_empty,
      shape, unchanged]
  | cons old tail =>
    simp [experiment_core.collections.replace_slice_first, core.slice.Slice.is_empty,
      shape, Slice.update, Slice.set, Slice.setAtNat]

theorem vector_transition (input : alloc.vec.Vec U8) (value : U8) :
    experiment_core.collections.replace_first input value =
      RustM.ok (!input.val.isEmpty, ⟨input.slice.set 0#usize value⟩) := by
  simp [experiment_core.collections.replace_first, alloc.vec.Vec.deref_mut, lift,
    slice_transition, alloc.vec.Vec.val]

theorem composition (input : alloc.vec.Vec U8) (value : U8) :
    replace_first input value =
      RustM.ok (!input.val.isEmpty, ⟨input.slice.set 0#usize value⟩) := by
  exact vector_transition input value

theorem preserves_length (input : alloc.vec.Vec U8) (value : U8) :
    ∃ changed updated, replace_first input value = RustM.ok (changed, updated) ∧
      updated.val = input.val.set 0 value ∧ updated.val.length = input.val.length := by
  refine ⟨_, _, composition input value, ?_, ?_⟩
  · simp [alloc.vec.Vec.val, Slice.set_val_eq]
  · simp [alloc.vec.Vec.val, Slice.set_val_eq]

theorem empty_unchanged (input : alloc.vec.Vec U8) (value : U8)
    (empty : input.val = []) :
    replace_first input value = RustM.ok (false, input) := by
  rw [composition]
  have emptySlice : input.slice.val = [] := empty
  have unchanged : (⟨input.slice.set 0#usize value⟩ : alloc.vec.Vec U8) = input := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.val, Slice.set_val_eq]
    rw [emptySlice]
    rfl
  simp [empty, unchanged]

theorem shared_core (input : alloc.vec.Vec U8) :
    experiment_core.collections.slice_length input = RustM.ok (alloc.vec.Vec.len input, input) := by
  unfold experiment_core.collections.slice_length
  apply congrArg RustM.ok
  apply Prod.ext
  · apply UScalar.eq_of_val_eq
    simp [alloc.vec.Vec.deref]
  · rfl

theorem shared_composition (input : alloc.vec.Vec U8) :
    slice_length input = RustM.ok (alloc.vec.Vec.len input, input) := shared_core input

theorem index_panic (input : Slice U8) (position : Usize) (value : U8)
    (outside : input.val.length ≤ position.val) :
    replace_at input position value = RustM.fail .panic := by
  simp [replace_at, experiment_core.collections.replace_at, Slice.update,
    List.getElem?_eq_none_iff.mpr outside]

end Collections.Properties
