module
public import GuardDriver.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace GuardDriver.Contracts
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

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

/-- The actual guard callee uses the checked first-party transition and retains
its reconstructed borrow. No acquisition or release is asserted here. -/
theorem callee_contract (guard : NativeGuard effects_core.Counter) (amount : U64) :
    effects_core.increment_guard guard amount = (do
      let (changed, updated) ← effects_core.increment guard.value amount
      .ok (changed, { guard with value := updated })) := by
  simp [effects_core.increment_guard, NativeGuard.deref_mut, NativeM.lift, NativeM.ok]

@[expose] def initial (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    guarded_suspending.closure :=
  ⟨mutex, amount, 0#u32, none, none, none, none⟩

@[expose] def saved (mutex : NativeMutex effects_core.Counter) (amount : U64)
    (changed : Bool) (guard : NativeGuard effects_core.Counter) : guarded_suspending.closure :=
  ⟨mutex, amount, 3#u32, some guard, some changed, some ⟨false, ⟨amount⟩⟩, some true⟩

@[expose] def completed (mutex : NativeMutex effects_core.Counter) (amount : U64)
    (changed : Bool) : guarded_suspending.closure :=
  ⟨mutex, amount, 1#u32, none, some changed, some ⟨false, ⟨amount⟩⟩, some false⟩

/-- Preserve the actual acquisition and mutation effects before Pending. -/
theorem first_poll (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    guarded_suspending.closure.poll ⟨initial mutex amount⟩
      (NativeTaskContext.fromWaker NativeWaker.noop) = (do
        let acquired ← NativeMutex.lock mutex
        let guard ← effects_core.recover_guard acquired
        let (changed, updated) ← effects_core.increment_guard guard amount
        Result.ok (.Pending, ⟨saved mutex amount changed updated⟩,
          NativeTaskContext.fromWaker NativeWaker.noop)) := by
  unfold guarded_suspending.closure.poll
  split <;> simp_all [initial, saved, effects_core.paused_counter,
    core.future.into_future.IntoFuture.Blanket.into_future,
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok,
    NativeTaskContext.fromWaker, NativeWaker.noop, NativeWaker.wakeByRef] <;>
      simp_all [UScalar.ofNatCore, UScalar.val]

/-- The second poll releases the very guard saved by the first. -/
theorem resumed_poll (mutex : NativeMutex effects_core.Counter) (amount : U64)
    (changed : Bool) (guard : NativeGuard effects_core.Counter) :
    guarded_suspending.closure.poll ⟨saved mutex amount changed guard⟩
      (NativeTaskContext.fromWaker NativeWaker.noop) = (do
        NativeGuard.release guard
        Result.ok (.Ready changed, ⟨completed mutex amount changed⟩,
          NativeTaskContext.fromWaker NativeWaker.noop)) := by
  unfold guarded_suspending.closure.poll
  split <;> simp_all [saved, completed,
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    effects_core.saturating_increment, core.pin.PinMutAT.get_mut,
    effects_core.release_guard, NativeOwnedDrop.drop, NativeM.ok,
    NativeTaskContext.fromWaker, NativeWaker.noop] <;>
      simp_all [UScalar.ofNatCore, UScalar.val]

theorem saved_drop (mutex : NativeMutex effects_core.Counter) (amount : U64)
    (changed : Bool) (guard : NativeGuard effects_core.Counter) :
    guarded_suspending.closure.drop_owned (saved mutex amount changed guard) =
      NativeGuard.release guard := rfl

theorem completed_drop (mutex : NativeMutex effects_core.Counter) (amount : U64) (changed : Bool) :
    guarded_suspending.closure.drop_owned (completed mutex amount changed) = Result.ok () := rfl

/-- Complete the actual compiler frame, releasing the guard after its second poll. -/
theorem finish_contract (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    finish_guarded mutex amount (NativeTaskContext.fromWaker NativeWaker.noop) = (do
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let (changed, updated) ← effects_core.increment_guard guard amount
      NativeGuard.release updated
      Result.ok (.Ready changed, NativeTaskContext.fromWaker NativeWaker.noop)) := by
  unfold finish_guarded
  change (do
    let (p, frame, context) ← guarded_suspending.closure.poll ⟨initial mutex amount⟩
      (NativeTaskContext.fromWaker NativeWaker.noop)
    let (result, context, frame) ← match p with
      | .Ready _ => Result.ok (p, context, frame.pointer)
      | .Pending => do
        let (result, frame, context) ← guarded_suspending.closure.poll frame context
        Result.ok (result, context, frame.pointer)
    guarded_suspending.closure.drop_owned frame
    Result.ok (result, context)) = _
  rw [first_poll]
  simp only [bind_assoc, Result.ok_bind, resumed_poll, completed_drop]

/-- Cancellation drops the actual suspended frame; earlier mutation is committed. -/
theorem cancel_contract (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    cancel_guarded mutex amount (NativeTaskContext.fromWaker NativeWaker.noop) = (do
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let (_, updated) ← effects_core.increment_guard guard amount
      NativeGuard.release updated
      Result.ok (true, NativeTaskContext.fromWaker NativeWaker.noop)) := by
  unfold cancel_guarded
  change (do
    let (p, frame, context) ← guarded_suspending.closure.poll ⟨initial mutex amount⟩
      (NativeTaskContext.fromWaker NativeWaker.noop)
    let cancelled ← match p with
      | .Ready _ => Result.ok false
      | .Pending => Result.ok true
    guarded_suspending.closure.drop_owned frame.pointer
    Result.ok (cancelled, context)) = _
  rw [first_poll]
  simp only [bind_assoc, Result.ok_bind, saved_drop]

end GuardDriver.Contracts
