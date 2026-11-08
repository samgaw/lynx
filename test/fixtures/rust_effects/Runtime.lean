module
public import Runtime.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.Properties

/-- The extracted cross-crate callee computes the sum or preserves the counter. -/
theorem increment_spec (counter : effects_core.Counter) (amount : U64) :
    ∃ success updated, effects_core.increment counter amount = Result.ok (success, updated) ∧
      (if success then updated.value.val = counter.value.val + amount.val
       else updated = counter ∧ U64.max < counter.value.val + amount.val) := by
  have arithmetic := U64.checked_add_bv_spec counter.value amount
  cases checked : U64.checked_add counter.value amount with
  | none =>
    refine ⟨false, counter, ?_, ?_⟩
    · simp [effects_core.increment, NativeM.lift, NativeM.ok, checked]
    · simpa [checked] using arithmetic
  | some value =>
    refine ⟨true, ⟨value⟩, ?_, ?_⟩
    · simp [effects_core.increment, NativeM.lift, NativeM.ok, checked]
    · have found := arithmetic
      simp only [checked] at found
      exact found.2.1

/-- Composition uses the callee's checked contract for both actual calls. -/
theorem twice_success (counter : effects_core.Counter) (first second : U64)
    (bounded : counter.value.val + first.val + second.val ≤ U64.max) :
    ∃ updated, increment_twice counter first second = Result.ok (true, updated) ∧
      updated.value.val = counter.value.val + first.val + second.val := by
  obtain ⟨success, intermediate, returned, property⟩ := increment_spec counter first
  cases success with
  | false => simp only [Bool.false_eq_true, ↓reduceIte] at property; omega
  | true =>
    simp only [↓reduceIte] at property
    obtain ⟨success, updated, returnedSecond, propertySecond⟩ := increment_spec intermediate second
    cases success with
    | false => simp only [Bool.false_eq_true, ↓reduceIte] at propertySecond; omega
    | true =>
      simp only [↓reduceIte] at propertySecond
      refine ⟨updated, ?_, by omega⟩
      simp [increment_twice, returned, returnedSecond]

/-- Rejection by the second call retains the completed first update. -/
theorem twice_second_overflow (counter : effects_core.Counter) (first second : U64)
    (bounded : counter.value.val + first.val ≤ U64.max)
    (overflow : U64.max < counter.value.val + first.val + second.val) :
    ∃ updated, increment_twice counter first second = Result.ok (false, updated) ∧
      updated.value.val = counter.value.val + first.val := by
  obtain ⟨success, intermediate, returned, property⟩ := increment_spec counter first
  cases success with
  | false => simp only [Bool.false_eq_true, ↓reduceIte] at property; omega
  | true =>
    simp only [↓reduceIte] at property
    obtain ⟨success, updated, returnedSecond, propertySecond⟩ := increment_spec intermediate second
    cases success with
    | true =>
      simp only [↓reduceIte] at propertySecond
      have maximum : updated.value.val ≤ U64.max := by scalar_tac
      omega
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at propertySecond
      refine ⟨updated, ?_, ?_⟩
      · simp [increment_twice, returned, returnedSecond]
      · rw [propertySecond.1, property]

theorem nonzero_success (value : U64) (nonzero : value ≠ 0#u64) :
    require_nonzero value = Result.ok value := by
  simp [require_nonzero, NativeM.massert, NativeM.ok, nonzero]

theorem zero_panics :
    require_nonzero 0#u64 = Result.error (.error (.atom "rust_panicked")) := by
  simp [require_nonzero, NativeM.massert, NativeM.fail]

theorem checked_next_success (value : U64) (bounded : value.val + 1 ≤ U64.max) :
    ∃ next, checked_next value = Result.ok next ∧ next.val = value.val + 1 := by
  have specification := U64.add_bv_spec (x := value) (y := 1#u64) bounded
  cases primitive : (value + 1#u64 : RustM U64) with
  | ret next =>
    simp only [primitive, WP.spec_ok] at specification
    refine ⟨next, ?_, specification.1⟩
    simp [checked_next, primitive]
  | vis effect continuation =>
    cases effect with
    | fail error => simp [primitive] at specification
  | div => simp [primitive] at specification

theorem checked_next_overflow :
    checked_next 18446744073709551615#u64 =
      Result.error (.error (.atom "rust_panicked")) := by
  have arithmetic := UScalar.add_equiv 18446744073709551615#u64 1#u64
  cases observed : (18446744073709551615#u64 + 1#u64 : RustM U64).match with
  | ok next => simp [observed] at arithmetic
  | div => simp [observed] at arithmetic
  | vis effect continuation =>
    cases effect with
    | fail error =>
      simp only [observed] at arithmetic
      obtain ⟨rfl, _⟩ := arithmetic
      simp [checked_next, NativeM.fromRust, observed, NativeM.fail]

/-- State already committed to the runtime is retained when native code panics. -/
theorem state_before_panic (before after : Environment) :
    (Result.nativeSet after (require_nonzero 0#u64)) before =
      (.error (.error (.atom "rust_panicked")), after) := by
  simp [zero_panics]

end Runtime.Properties
