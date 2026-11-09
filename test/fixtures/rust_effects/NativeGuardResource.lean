module
public import Shared.Critical
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Shared.Guarded
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

@[expose] def initial (resource : NativeResourceArc CounterResource) (amount : U64) :
    guarded_resource_suspending.closure :=
  ⟨some resource, amount, 0#u32, none, none, none, none, none, none⟩

@[expose] def pending (resource : NativeResourceArc CounterResource) (amount : U64)
    (changed : Bool) (guard : NativeGuard effects_core.Counter) :
    guarded_resource_suspending.closure :=
  ⟨none, amount, 3#u32, some resource, some guard, some changed,
    some ⟨false, ⟨amount⟩⟩, some true, some true⟩

@[expose] def completed (amount : U64) (changed : Bool) :
    guarded_resource_suspending.closure :=
  ⟨none, amount, 1#u32, none, none, some changed, some ⟨false, ⟨amount⟩⟩, some false, some false⟩

theorem first_poll (resource : NativeResourceArc CounterResource) (amount : U64) :
    guarded_resource_suspending.closure.poll ⟨initial resource amount⟩
      (NativeTaskContext.fromWaker NativeWaker.noop) = (do
        let payload ← NativeResourceArc.deref resource
        let acquired ← NativeMutex.lock payload.state
        let guard ← effects_core.recover_guard acquired
        let (changed, updated) ← effects_core.increment_guard guard amount
        Result.ok (.Pending, ⟨pending resource amount changed updated⟩,
          NativeTaskContext.fromWaker NativeWaker.noop)) := by
  unfold guarded_resource_suspending.closure.poll
  split <;> simp_all [initial, pending, core.mem.replace, effects_core.paused_counter,
    core.future.into_future.IntoFuture.Blanket.into_future,
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok, NativeTaskContext.fromWaker,
    NativeWaker.noop, NativeWaker.wakeByRef] <;> simp_all [UScalar.ofNatCore, UScalar.val]

theorem resumed_poll (resource : NativeResourceArc CounterResource) (amount : U64)
    (changed : Bool) (guard : NativeGuard effects_core.Counter) :
    guarded_resource_suspending.closure.poll ⟨pending resource amount changed guard⟩
      (NativeTaskContext.fromWaker NativeWaker.noop) = (do
        NativeGuard.release guard
        resource_release resource
        Result.ok (.Ready changed, ⟨completed amount changed⟩,
          NativeTaskContext.fromWaker NativeWaker.noop)) := by
  unfold guarded_resource_suspending.closure.poll
  split <;> simp_all [pending, completed, core.mem.replace,
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    effects_core.saturating_increment, core.pin.PinMutAT.get_mut,
    effects_core.release_guard, NativeOwnedDrop.drop, NativeM.ok,
    NativeTaskContext.fromWaker, NativeWaker.noop] <;> simp_all [UScalar.ofNatCore, UScalar.val]

/-- The real compiler destructor releases the saved guard before its resource. -/
theorem pending_drop (resource : NativeResourceArc CounterResource) (amount : U64)
    (changed : Bool) (guard : NativeGuard effects_core.Counter) :
    guarded_resource_suspending.closure.drop_owned (pending resource amount changed guard) = (do
      NativeGuard.release guard
      resource_release resource) := rfl

theorem initial_drop (resource : NativeResourceArc CounterResource) (amount : U64) :
    guarded_resource_suspending.closure.drop_owned (initial resource amount) =
      resource_release resource := rfl

theorem completed_drop (amount : U64) (changed : Bool) :
    guarded_resource_suspending.closure.drop_owned (completed amount changed) = Result.ok () := rfl

theorem finish_driver (resource : NativeResourceArc CounterResource) (amount : U64) :
    finish_guarded_resource resource amount (NativeTaskContext.fromWaker NativeWaker.noop) = (do
      let payload ← NativeResourceArc.deref resource
      let acquired ← NativeMutex.lock payload.state
      let guard ← effects_core.recover_guard acquired
      let (changed, updated) ← effects_core.increment_guard guard amount
      NativeGuard.release updated
      resource_release resource
      Result.ok (.Ready changed, NativeTaskContext.fromWaker NativeWaker.noop)) := by
  simp only [finish_guarded_resource, guarded_resource_suspending, NativeM.ok,
    monadLift_self, Result.ok_bind]
  change (do
    let (p, frame, context) ← guarded_resource_suspending.closure.poll ⟨initial resource amount⟩
      (NativeTaskContext.fromWaker NativeWaker.noop)
    let (result, context, frame) ← match p with
      | .Ready _ => Result.ok (p, context, frame.pointer)
      | .Pending => do
        let (result, frame, context) ← guarded_resource_suspending.closure.poll frame context
        Result.ok (result, context, frame.pointer)
    guarded_resource_suspending.closure.drop_owned frame
    Result.ok (result, context)) = _
  rw [first_poll]
  simp only [bind_assoc, Result.ok_bind, resumed_poll, completed_drop]

theorem cancel_driver (resource : NativeResourceArc CounterResource) (amount : U64) :
    cancel_guarded_resource resource amount (NativeTaskContext.fromWaker NativeWaker.noop) = (do
      let payload ← NativeResourceArc.deref resource
      let acquired ← NativeMutex.lock payload.state
      let guard ← effects_core.recover_guard acquired
      let (_, updated) ← effects_core.increment_guard guard amount
      NativeGuard.release updated
      resource_release resource
      Result.ok (true, NativeTaskContext.fromWaker NativeWaker.noop)) := by
  simp only [cancel_guarded_resource, guarded_resource_suspending, NativeM.ok,
    monadLift_self, Result.ok_bind]
  change (do
    let (p, frame, context) ← guarded_resource_suspending.closure.poll ⟨initial resource amount⟩
      (NativeTaskContext.fromWaker NativeWaker.noop)
    let cancelled ← match p with
      | .Ready _ => Result.ok false
      | .Pending => Result.ok true
    guarded_resource_suspending.closure.drop_owned frame.pointer
    Result.ok (cancelled, context)) = _
  rw [first_poll]
  simp only [bind_assoc, Result.ok_bind, pending_drop]

/-- Exact equality of effects, including owner release, allows reuse under interleavings. -/
@[cbv_eval] theorem finish_contract (resource : NativeResourceArc CounterResource) (amount : U64) :
    __FINISH__ resource amount = __ADD__ resource amount := by
  simp only [__FINISH__, finish_driver, __ADD__, resource_locked_increment,
    effects_core.locked_increment, effects_core.update_release, NativeM.ok,
    NativeOwnedDrop.drop, monadLift_self, bind_assoc, Result.ok_bind]

/-- Cancellation acknowledges Pending; the checked mutation still commits. -/
@[cbv_eval] theorem cancel_contract (resource : NativeResourceArc CounterResource) (amount : U64) :
    __CANCEL__ resource amount = (do
      let _ ← __ADD__ resource amount
      Result.ok true) := by
  simp only [__CANCEL__, cancel_driver, __ADD__, resource_locked_increment,
    effects_core.locked_increment, effects_core.update_release, NativeM.ok,
    NativeOwnedDrop.drop, monadLift_self, bind_assoc, Result.ok_bind]

end Shared.Guarded
