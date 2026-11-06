module
public import Runtime.NativeDrop.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.NativeDropProperties

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

theorem explicit_dispose (value : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_discard_scalar value env = (.ok (), { env with refCounter := env.refCounter + 1 }) := by
  simpa [mutex_discard_scalar, NativeDrop.drop] using NativeMutex.new_dispose value env fresh

theorem scope_dispose (value : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_scope_scalar value env = (.ok (), { env with refCounter := env.refCounter + 1 }) := by
  simpa [mutex_scope_scalar, NativeDrop.drop] using NativeMutex.new_dispose value env fresh

theorem scope_result (value : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_scope_flag value env = (.ok true, { env with refCounter := env.refCounter + 1 }) := by
  simpa [mutex_scope_flag, NativeDrop.drop, NativeM.ok] using
    NativeMutex.new_dispose_next value (Result.ok true) env fresh

theorem checked_dispose (value amount : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_checked_discard value amount env =
      (.ok (decide (value.val + amount.val ≤ U64.max)), { env with refCounter := env.refCounter + 1 }) := by
  obtain ⟨success, counter, returned, property⟩ := increment_spec ⟨value⟩ amount
  have flag : success = decide (value.val + amount.val ≤ U64.max) := by
    cases success with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at property
      have bound : ¬ (value.val + amount.val ≤ U64.max) := by omega
      simp [bound]
    | true =>
      simp only [↓reduceIte] at property
      have maximum : counter.value.val ≤ U64.max := by scalar_tac
      have bound : value.val + amount.val ≤ U64.max := by simpa [property] using maximum
      simp [bound]
  have lifecycle := NativeMutex.new_dispose_next counter.value (Result.ok success) env fresh
  simpa [mutex_checked_discard, returned, NativeDrop.drop, NativeM.ok, flag] using lifecycle

theorem dispose_before_assert (value : U64) (accepted : Bool) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    mutex_dispose_then_assert value accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with refCounter := env.refCounter + 1 }) := by
  have lifecycle := NativeMutex.new_dispose_next value
    (do NativeM.massert (accepted = true); NativeM.ok ()) env fresh
  cases accepted <;>
    simpa [mutex_dispose_then_assert, NativeDrop.drop, NativeM.ok, NativeM.massert, NativeM.fail] using lifecycle

theorem consume_owned (mutex : NativeMutex U64) (value : U64) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName U64,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])]) :
    mutex_consume_scalar mutex env =
      (.ok (), { env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != mutex.id) }) := by
  simp [mutex_consume_scalar, NativeDrop.drop, NativeMutex.dispose, NativeM.readCell,
    NativeM.removeCell, stored, NativeCodec.roundtrip]

end Runtime.NativeDropProperties
