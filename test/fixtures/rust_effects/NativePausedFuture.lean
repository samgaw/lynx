module
public import Poll.Extraction.Funs
public section
open Aeneas Aeneas.Std effects_native Lynx
namespace Poll.Properties

theorem initial_state (value : U64) :
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
      [(waker.id, NativeWaker.typeName, .atom "idle")]) :
    (effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll
        ⟨⟨true, ⟨value⟩⟩⟩ ⟨waker⟩ >>= next) env =
      next (core.task.poll.Poll.Pending, ⟨⟨false, ⟨value⟩⟩⟩, ⟨waker⟩) (NativeWaker.notifiedEnv waker env) := by
  simpa [effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok, bind_assoc, NativeWaker.notifiedEnv] using
    (NativeWaker.wakeByRef_registered_next waker
      (fun _ => next (core.task.poll.Poll.Pending, ⟨⟨false, ⟨value⟩⟩⟩, ⟨waker⟩)) env bounded stored)

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

theorem caller_pending (value : U64) (waker : NativeWaker) (env : Environment) (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")]) :
    (do
      let future ← effects_core.paused_counter value
      poll_paused ⟨future⟩ ⟨waker⟩) env =
      (.ok (core.task.poll.Poll.Pending, ⟨⟨false, ⟨value⟩⟩⟩, ⟨waker⟩), NativeWaker.notifiedEnv waker env) := by
  have model := callee_pending value waker Result.ok env bounded stored
  simpa [effects_core.paused_counter, poll_paused, NativeM.ok] using model

theorem no_early_completion (value result : U64) (waker : NativeWaker) (env : Environment) (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")])
    (finalState : effects_native.core.pin.Pin effects_core.PausedCounter)
    (context : NativeTaskContext) (finalEnv : Environment) :
    (do
      let future ← effects_core.paused_counter value
      poll_paused ⟨future⟩ ⟨waker⟩) env ≠
      (.ok (core.task.poll.Poll.Ready result, finalState, context), finalEnv) := by
  rw [caller_pending value waker env bounded stored]
  simp

/-- A second explicit poll completes; no executor fairness or implicit repoll is assumed. -/
theorem two_polls (value : U64) (waker : NativeWaker) (env : Environment) (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, NativeWaker.typeName, .atom "idle")]) :
    ∃ result,
      (do
        let future ← effects_core.paused_counter value
        let (first, updated, context) ← poll_paused ⟨future⟩ ⟨waker⟩
        let (second, finalState, _) ← poll_paused updated context
        Result.ok (first, second, finalState)) env =
          (.ok (core.task.poll.Poll.Pending, core.task.poll.Poll.Ready result,
            ⟨⟨false, ⟨value⟩⟩⟩), NativeWaker.notifiedEnv waker env) ∧
      result.val = min U64.max (value.val + 1) := by
  obtain ⟨result, computed, arithmetic⟩ := callee_ready value ⟨waker⟩
  refine ⟨result, ?_, arithmetic⟩
  have model := callee_pending value waker
    (fun output => do
      let (first, updated, context) := output
      let (second, finalState, _) ← poll_paused updated context
      Result.ok (first, second, finalState)) env bounded stored
  simpa [effects_core.paused_counter, poll_paused, NativeM.ok, computed] using model

end Poll.Properties
