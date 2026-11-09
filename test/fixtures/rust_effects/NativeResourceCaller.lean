module
public import Macro.Properties
public section
open Aeneas Aeneas.Std Lynx effects_native Macro.Properties
namespace Macro.Caller

/-- The actual caller invokes the extracted poll and the actual compiler drop. -/
theorem caller_contract (resource : NativeResourceArc CounterResource) (amount : U64)
    (context : NativeTaskContext) :
    poll_cancel_resource resource amount context = (do
      let future ← resource_suspending resource amount
      let (reply, retained, context) ← resource_suspending.closure.poll ⟨future⟩ context
      resource_suspending.closure.drop_owned retained.pointer
      Result.ok (reply, context)) := by
  simp [poll_cancel_resource, NativeM.ok]

/-- A real Rust caller cancels its Pending future at scope exit, reclaiming the
sole resource owner and mutex while retaining the registered wake notification. -/
theorem caller_cancellation (value amount : U64) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous) :
    poll_cancel_resource ⟨2,3⟩ amount ⟨⟨0, false⟩⟩ (live env value 3 false) =
      (.ok (.Pending, ⟨⟨0, false⟩⟩), reclaimed env 3 true) := by
  rw [caller_contract]
  simp only [initial_state, Result.ok_bind, bind_assoc]
  have pending := first_pending_next value amount env (fun (reply, retained, context) => do
    resource_suspending.closure.drop_owned retained.pointer
    Result.ok (reply, context))
  dsimp only at pending
  rw [pending]
  change (resource_release ⟨2,3⟩ >>= fun _ => Result.ok ((core.task.poll.Poll.Pending : core.task.poll.Poll Bool), (⟨⟨0, false⟩⟩ : NativeTaskContext))) _ = _
  simpa using release_next value 3 true env policy
    (fun _ => Result.ok ((core.task.poll.Poll.Pending : core.task.poll.Poll Bool), (⟨⟨0, false⟩⟩ : NativeTaskContext)))

@[expose] def readyInitial (amount : U64) : resource_immediate.closure :=
  ⟨some ⟨2,3⟩, amount, 0#u32⟩
@[expose] def readyCompleted (amount : U64) : resource_immediate.closure :=
  ⟨none, amount, 1#u32⟩

theorem ready_poll_contract (amount : U64) (context : NativeTaskContext) :
    resource_immediate.closure.poll ⟨readyInitial amount⟩ context = (do
      let changed ← resource_locked_increment ⟨2,3⟩ amount
      resource_release ⟨2,3⟩
      Result.ok (.Ready changed, ⟨readyCompleted amount⟩, context)) := by
  simp [resource_immediate.closure.poll, readyInitial, readyCompleted, core.mem.replace,
    NativeM.ok, UScalar.ofNatCore, UScalar.val]

theorem completed_cleanup (amount : U64) :
    resource_immediate.closure.drop_owned (readyCompleted amount) = Result.ok () := rfl

theorem ready_caller_contract (resource : NativeResourceArc CounterResource) (amount : U64)
    (context : NativeTaskContext) :
    poll_ready_resource resource amount context = (do
      let future ← resource_immediate resource amount
      let (reply, retained, context) ← resource_immediate.closure.poll ⟨future⟩ context
      resource_immediate.closure.drop_owned retained.pointer
      Result.ok (reply, context)) := by
  simp [poll_ready_resource, NativeM.ok]

theorem caller_completion (value amount : U64) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous) :
    ∃ changed updated,
      poll_ready_resource ⟨2,3⟩ amount ⟨⟨0, false⟩⟩ (live env value 3 false) =
        (.ok (.Ready changed, ⟨⟨0, false⟩⟩), reclaimed env 4 false) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  have created : resource_immediate ⟨2,3⟩ amount = Result.ok (readyInitial amount) := rfl
  rw [ready_caller_contract]
  simp only [created, Result.ok_bind, bind_assoc]
  rw [ready_poll_contract]
  simp only [bind_assoc, Result.ok_bind, completed_cleanup]
  let finish : Bool → NativeM (core.task.poll.Poll Bool × NativeTaskContext) := fun changed => do
    resource_release ⟨2,3⟩
    Result.ok (.Ready changed, ⟨⟨0, false⟩⟩)
  obtain ⟨changed, updated, computed, arithmetic⟩ := update_next value amount env false finish
  refine ⟨changed, updated, ?_, arithmetic⟩
  change (resource_locked_increment ⟨2,3⟩ amount >>= finish).run (live env value 3 false) = _
  dsimp only at computed
  rw [computed]
  simpa [finish] using release_next updated 4 false env policy
    (fun _ => Result.ok ((core.task.poll.Poll.Ready changed : core.task.poll.Poll Bool), (⟨⟨0, false⟩⟩ : NativeTaskContext)))

end Macro.Caller
