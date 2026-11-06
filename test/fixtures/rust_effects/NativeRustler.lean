module
public import RuntimeNif.Extraction.Funs
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace RuntimeNif.Properties

/-- The actual internal algorithm either computes the sum or rejects overflow. -/
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

theorem internal_state (value amount : U64) (env : Environment)
    (empty : env.nativeHeap = []) :
    ∃ changed, mutex_locked_scalar value amount env =
      (.ok changed, { env with refCounter := env.refCounter + 2 }) ∧
      changed = decide (value.val + amount.val ≤ U64.max) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec ⟨value⟩ amount
  refine ⟨changed, ?_, ?_⟩
  · simp [mutex_locked_scalar, effects_core.locked_scalar_increment, NativeMutex.new, NativeM.allocate,
      NativeMutex.lock, NativeM.ok, empty, bind_assoc]
    rw [Result.wait_ready_apply _ _ _ _ _ (by
      simp [NativeMutex.pollLock, NativeCodec.roundtrip]
      constructor <;> rfl)]
    simp [NativeGuard.deref, NativeGuard.deref_mut, NativeM.lift,
      NativeDrop.drop, NativeGuard.release, returned]
    rw [Result.wait_ready_apply _ _ _ _ _ (by
      simp [NativeGuard.pollRelease, NativeCodec.roundtrip]
      constructor <;> rfl)]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell,
      NativeCodec.roundtrip, Nat.add_assoc]
  · cases changed with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at property
      have outside : ¬ (value.val + amount.val ≤ U64.max) := by omega
      simp [outside]
    | true =>
      simp only [↓reduceIte] at property
      have maximum : updated.value.val ≤ U64.max := by scalar_tac
      have bound : value.val + amount.val ≤ U64.max := by simpa [property] using maximum
      simp [bound]

theorem facade_adapter_continuation {β : Type} (value amount : U64)
    (next : Term → Result β) (env : Environment) (empty : env.nativeHeap = []) :
    (do
      let encoded ← Rustler.executeNative
        (__CHECKED__ value amount) Rustler.encodeBool
      next encoded) env =
      next (Rustler.encodeBool (decide (value.val + amount.val ≤ U64.max)))
        { env with refCounter := env.refCounter + 2 } := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec ⟨value⟩ amount
  have flag : changed = decide (value.val + amount.val ≤ U64.max) := by
    cases changed with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at property
      have outside : ¬ (value.val + amount.val ≤ U64.max) := by omega
      simp [outside]
    | true =>
      simp only [↓reduceIte] at property
      have maximum : updated.value.val ≤ U64.max := by scalar_tac
      have bound : value.val + amount.val ≤ U64.max := by simpa [property] using maximum
      simp [bound]
  simp [Rustler.executeNative, Result.handle, __CHECKED__,
    mutex_locked_scalar, effects_core.locked_scalar_increment, NativeMutex.new, NativeM.allocate,
    NativeMutex.lock, NativeM.ok, empty, bind_assoc]
  rw [Result.wait_ready_apply _ _ _ _ _ (by
    simp [NativeMutex.pollLock, NativeCodec.roundtrip]
    constructor <;> rfl)]
  simp [NativeGuard.deref, NativeGuard.deref_mut, NativeM.lift,
    NativeDrop.drop, NativeGuard.release, returned, Result.handle]
  rw [Result.wait_ready_apply _ _ _ _ _ (by
    simp [NativeGuard.pollRelease, NativeCodec.roundtrip]
    constructor <;> rfl)]
  simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell,
    NativeCodec.roundtrip, Nat.add_assoc, flag, Result.handle]

theorem released_adapter_continuation {β : Type} (value : U64) (accepted : Bool)
    (next : Term → Result β) (env : Environment) (empty : env.nativeHeap = []) :
    (do
      let encoded ← Rustler.executeNative
        (__RELEASED__ value accepted) Rustler.encodeBool
      next encoded) env =
      if accepted then next Term.true { env with refCounter := env.refCounter + 1 }
      else (.error (.error (.atom "nif_panicked")), { env with refCounter := env.refCounter + 1 }) := by
  cases accepted <;>
    simp [__RELEASED__,
      mutex_dispose_then_assert, Rustler.executeNative, Result.handle,
      NativeMutex.new, NativeM.allocate, NativeDrop.drop, NativeMutex.dispose,
      NativeM.readCell, NativeM.removeCell, NativeCodec.roundtrip,
      NativeM.massert, NativeM.fail, NativeM.ok, empty, Rustler.encodeBool]

theorem released_handler_continuation {β : Type} (value : U64) (accepted : Bool)
    (next : Term → Result β) (handler : Exception → Result β)
    (env : Environment) (empty : env.nativeHeap = []) :
    Result.tryWith (Rustler.executeNative (__RELEASED__ value accepted) Rustler.encodeBool)
      next handler env =
      if accepted then next Term.true { env with refCounter := env.refCounter + 1 }
      else handler (.error (.atom "nif_panicked")) { env with refCounter := env.refCounter + 1 } := by
  cases accepted <;>
    simp [__RELEASED__, mutex_dispose_then_assert, Rustler.executeNative,
      Result.tryWith, Result.handle, Result.bind, NativeMutex.new, NativeM.allocate, NativeDrop.drop,
      NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeCodec.roundtrip,
      NativeM.massert, NativeM.fail, NativeM.ok, empty, Rustler.encodeBool]

end RuntimeNif.Properties
