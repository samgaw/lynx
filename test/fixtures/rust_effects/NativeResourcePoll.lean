module
public import Shared.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Shared.Future

theorem ready_poll (resource : NativeResourceArc CounterResource) (amount : U64)
    (context : NativeTaskContext) :
    resource_immediate.closure.poll ⟨⟨some resource, amount, 0#u32⟩⟩ context = (do
      let changed ← resource_locked_increment resource amount
      resource_release resource
      Result.ok (.Ready changed, ⟨⟨none, amount, 1#u32⟩⟩, context)) := by
  simp [resource_immediate.closure.poll, core.mem.replace, NativeM.ok, UScalar.ofNatCore]

theorem ready_drop (amount : U64) :
    resource_immediate.closure.drop_owned ⟨none, amount, 1#u32⟩ = Result.ok () := rfl

/-- This compiled Rustler function constructs its own standard Context and
completes the actual compiler future, including its real destructor. -/
theorem add_contract (resource : NativeResourceArc CounterResource) (amount : U64) :
    __ADD__ resource amount = (do
      let changed ← resource_locked_increment resource amount
      resource_release resource
      Result.ok changed) := by
  simp only [__ADD__, poll_ready_resource, resource_immediate,
    NativeM.ok, monadLift_self, Result.ok_bind, ready_poll, bind_assoc, ready_drop]

@[expose] def pending (resource : NativeResourceArc CounterResource) (amount : U64) :
    resource_suspending.closure :=
  ⟨none, amount, 3#u32, some resource, some amount, some ⟨false, ⟨amount⟩⟩, some true⟩

theorem pending_poll (resource : NativeResourceArc CounterResource) (amount : U64) :
    resource_suspending.closure.poll
      ⟨⟨some resource, amount, 0#u32, none, none, none, none⟩⟩
      (NativeTaskContext.fromWaker NativeWaker.noop) =
        Result.ok (.Pending, ⟨pending resource amount⟩,
          NativeTaskContext.fromWaker NativeWaker.noop) := by
  simp [resource_suspending.closure.poll, pending, core.mem.replace,
    effects_core.paused_counter, core.future.into_future.IntoFuture.Blanket.into_future,
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok, bind_assoc, UScalar.ofNatCore,
    NativeTaskContext.fromWaker, NativeWaker.noop, NativeWaker.wakeByRef]

theorem pending_drop (resource : NativeResourceArc CounterResource) (amount : U64) :
    resource_suspending.closure.drop_owned (pending resource amount) = resource_release resource := rfl

/-- Pending is cancelled at scope exit. A no-op wake never implies completion. -/
theorem cancel_contract (resource : NativeResourceArc CounterResource) (amount : U64) :
    __CANCEL__ resource amount = (do
      resource_release resource
      Result.ok true) := by
  simp only [__CANCEL__, poll_cancel_resource, resource_suspending,
    NativeM.ok, monadLift_self, Result.ok_bind, pending_poll, bind_assoc, pending_drop]

end Shared.Future
