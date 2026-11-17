module
public import __PREFIX__.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace __PREFIX__.Properties

@[expose] def retained {α : Type} (input : alloc.vec.Vec α) : alloc.vec.Vec α :=
  alloc.vec.Vec.from input.val.dropLast (by
    have bound := input.property
    simp only [List.length_dropLast]
    omega)

theorem internal_spec (α : Type) (input : alloc.vec.Vec α) :
    __CORE__.pop_last (T := α) input = RustM.ok (input.val.getLast?, retained input) := by
  rfl

theorem composition (input : alloc.vec.Vec I64) :
    __ANALYSIS__.pop_record input = RustM.ok (input.val.getLast?, retained input) := by
  simpa [__ANALYSIS__.pop_record] using internal_spec I64 input

theorem empty_unchanged :
    __ANALYSIS__.pop_record (alloc.vec.Vec.new I64) =
      RustM.ok (none, alloc.vec.Vec.new I64) := by
  rw [composition]
  rfl

theorem last_and_prefix (initial : List I64) (last : I64)
    (bounded : (initial ++ [last]).length ≤ Usize.max) :
    __ANALYSIS__.pop_record (alloc.vec.Vec.from (initial ++ [last]) bounded) =
      RustM.ok (some last, alloc.vec.Vec.from initial (by
        have h := bounded
        simp only [List.length_append, List.length_singleton] at h
        omega)) := by
  rw [composition]
  simp [retained]

theorem length_decreases (input : alloc.vec.Vec I64) :
    ∃ removed output, __ANALYSIS__.pop_record input = RustM.ok (removed, output) ∧
      output.val.length = input.val.length - 1 := by
  refine ⟨_, _, composition input, ?_⟩
  simp [retained]

end __PREFIX__.Properties
