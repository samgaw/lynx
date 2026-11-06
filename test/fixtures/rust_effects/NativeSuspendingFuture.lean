module
public import Suspend.Extraction.Funs
public section
open Aeneas Aeneas.Std effects_native Lynx
namespace Suspend.Properties

theorem internal_initial_state (value : U64) :
    effects_core.paused_counter value = Result.ok ⟨true, ⟨value⟩⟩ := rfl

theorem core_increment (value : U64) :
    ∃ result, effects_core.saturating_increment value = Result.ok result ∧
      result.val = min U64.max (value.val + 1) := by
  refine ⟨core.num.U64.saturating_add value 1#u64, rfl, ?_⟩
  simp

/-- The Pending path retains progress and requests the registered wake before returning. -/
theorem callee_pending {α : Type} (value : U64) (waker : NativeWaker)
    (next : (core.task.poll.Poll U64 × effects_native.core.pin.Pin effects_core.PausedCounter × NativeTaskContext) → Result α)
    (env : Environment) (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")])
    (callback : waker.isNoop = false) :
    (effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll
        ⟨⟨true, ⟨value⟩⟩⟩ ⟨waker⟩ >>= next) env =
      next (core.task.poll.Poll.Pending, ⟨⟨false, ⟨value⟩⟩⟩, ⟨waker⟩) (NativeWaker.notifiedEnv waker env) := by
  simpa [effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok, bind_assoc, NativeWaker.notifiedEnv, callback] using
    (NativeWaker.wakeByRef_registered_next waker
      (fun _ => next (core.task.poll.Poll.Pending, ⟨⟨false, ⟨value⟩⟩⟩, ⟨waker⟩)) env bounded stored callback)

theorem callee_ready (value : U64) (context : NativeTaskContext) :
    ∃ result,
      effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll
          ⟨⟨false, ⟨value⟩⟩⟩ context =
        Result.ok (core.task.poll.Poll.Ready result, ⟨⟨false, ⟨value⟩⟩⟩, context) ∧
      result.val = min U64.max (value.val + 1) := by
  obtain ⟨result, computed, arithmetic⟩ := core_increment value
  refine ⟨result, ?_, arithmetic⟩
  simp [effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok, computed]

theorem initial_state (value : U64) :
    suspended_increment value = Result.ok ⟨value, 0#u32, none⟩ := rfl

/-- Compose the actual compiler poll with the proved first-party Pending transition. -/
theorem first_pending_next {α : Type} (value : U64) (waker : NativeWaker)
    (next : (core.task.poll.Poll U64 × effects_native.core.pin.Pin suspended_increment.closure × NativeTaskContext) → Result α)
    (env : Environment) (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")])
    (callback : waker.isNoop = false) :
    (suspended_increment.closure.poll ⟨⟨value, 0#u32, none⟩⟩ ⟨waker⟩ >>= next) env =
      next (.Pending, ⟨⟨value, 3#u32, some ⟨false, ⟨value⟩⟩⟩⟩, ⟨waker⟩)
        (NativeWaker.notifiedEnv waker env) := by
  let after : (core.task.poll.Poll U64 × effects_native.core.pin.Pin effects_core.PausedCounter × NativeTaskContext) →
      Result (core.task.poll.Poll U64 × effects_native.core.pin.Pin suspended_increment.closure × NativeTaskContext) :=
    fun output => match output.1 with
    | .Ready _ => Result.ok (output.1, ⟨⟨value, 1#u32, some output.2.1.pointer⟩⟩, output.2.2)
    | .Pending => Result.ok (.Pending, ⟨⟨value, 3#u32, some output.2.1.pointer⟩⟩, output.2.2)
  have unfolded : suspended_increment.closure.poll ⟨⟨value, 0#u32, none⟩⟩ ⟨waker⟩ =
      (effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll ⟨⟨true, ⟨value⟩⟩⟩ ⟨waker⟩ >>= after) := by rfl
  rw [unfolded]
  have composed := callee_pending value waker (fun output => after output >>= next) env bounded stored callback
  simpa [after, bind_assoc] using composed

theorem first_pending (value : U64) (waker : NativeWaker) (env : Environment)
    (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")])
    (callback : waker.isNoop = false) :
    suspended_increment.closure.poll ⟨⟨value, 0#u32, none⟩⟩ ⟨waker⟩ env =
      (.ok (.Pending, ⟨⟨value, 3#u32, some ⟨false, ⟨value⟩⟩⟩⟩, ⟨waker⟩),
        NativeWaker.notifiedEnv waker env) := by
  simpa using first_pending_next value waker Result.ok env bounded stored callback

theorem resume_ready (value : U64) (context : NativeTaskContext) :
    ∃ result,
      suspended_increment.closure.poll ⟨⟨value, 3#u32, some ⟨false, ⟨value⟩⟩⟩⟩ context =
        Result.ok (.Ready result, ⟨⟨value, 1#u32, some ⟨false, ⟨value⟩⟩⟩⟩, context) ∧
      result.val = min U64.max (value.val + 1) := by
  obtain ⟨result, computed, arithmetic⟩ := callee_ready value context
  refine ⟨result, ?_, arithmetic⟩
  let after : (core.task.poll.Poll U64 × effects_native.core.pin.Pin effects_core.PausedCounter × NativeTaskContext) →
      Result (core.task.poll.Poll U64 × effects_native.core.pin.Pin suspended_increment.closure × NativeTaskContext) :=
    fun output => match output.1 with
    | .Ready _ => Result.ok (output.1, ⟨⟨value, 1#u32, some output.2.1.pointer⟩⟩, output.2.2)
    | .Pending => Result.ok (.Pending, ⟨⟨value, 3#u32, some output.2.1.pointer⟩⟩, output.2.2)
  have unfolded : suspended_increment.closure.poll ⟨⟨value, 3#u32, some ⟨false, ⟨value⟩⟩⟩⟩ context =
      (effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll ⟨⟨false, ⟨value⟩⟩⟩ context >>= after) := by rfl
  rw [unfolded, computed]
  rfl

/-- A missing compiler saved value is a verification cutoff, not a Rust panic. -/
theorem missing_saved_slot (value : U64) (context : NativeTaskContext) :
    suspended_increment.closure.poll ⟨⟨value, 3#u32, none⟩⟩ context =
      Result.error .exhausted := rfl

theorem exhaustion_not_catchable (value : U64) (context : NativeTaskContext)
    (next : (core.task.poll.Poll U64 × effects_native.core.pin.Pin suspended_increment.closure × NativeTaskContext) → Result Unit)
    (handler : Exception → Result Unit) :
    Result.tryWith (suspended_increment.closure.poll ⟨⟨value, 3#u32, none⟩⟩ context) next handler =
      Result.error .exhausted := by
  rw [missing_saved_slot, Result.tryWith_exhausted]

theorem repoll_completed (value : U64) (context : NativeTaskContext) :
    suspended_increment.closure.poll ⟨⟨value, 1#u32, some ⟨false, ⟨value⟩⟩⟩⟩ context =
      Result.error (.error (.atom "rust_panicked")) := rfl

theorem two_polls (value : U64) (waker : NativeWaker) (env : Environment)
    (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")])
    (callback : waker.isNoop = false) :
    ∃ result,
      (do
        let future ← suspended_increment value
        let (first, updated, context) ← suspended_increment.closure.poll ⟨future⟩ ⟨waker⟩
        let (second, finalState, _) ← suspended_increment.closure.poll updated context
        Result.ok (first, second, finalState)) env =
          (.ok (.Pending, .Ready result, ⟨⟨value, 1#u32, some ⟨false, ⟨value⟩⟩⟩⟩),
            NativeWaker.notifiedEnv waker env) ∧
      result.val = min U64.max (value.val + 1) := by
  obtain ⟨result, computed, arithmetic⟩ := resume_ready value ⟨waker⟩
  refine ⟨result, ?_, arithmetic⟩
  have composed := first_pending_next value waker
    (fun output => do
      let (first, updated, context) := output
      let (second, finalState, _) ← suspended_increment.closure.poll updated context
      Result.ok (first, second, finalState)) env bounded stored callback
  simpa [suspended_increment, NativeM.ok, computed] using composed

end Suspend.Properties
