module
public import Effects.Extraction.Funs
public section
open Aeneas Aeneas.Std effects_core
namespace Effects.Properties

/-- The actual mutable Rust transition preserves state on overflow and computes
the mathematical sum on success. It makes no claim about acquiring a lock. -/
theorem increment_spec (counter : Counter) (amount : U64) :
    ∃ success updated, increment counter amount = RustM.ok (success, updated) ∧
      (if success then updated.value.val = counter.value.val + amount.val
       else updated = counter ∧ U64.max < counter.value.val + amount.val) := by
  have arithmetic := U64.checked_add_bv_spec counter.value amount
  cases checked : U64.checked_add counter.value amount with
  | none =>
    refine ⟨false, counter, ?_, ?_⟩
    · simp [increment, lift, checked]
    · simpa [checked] using arithmetic
  | some value =>
    refine ⟨true, ⟨value⟩, ?_, ?_⟩
    · simp [increment, lift, checked]
    · have found := arithmetic
      simp only [checked] at found
      exact found.2.1

end Effects.Properties
