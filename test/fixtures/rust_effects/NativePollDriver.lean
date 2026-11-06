module
public import Driver.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Driver.Properties

theorem callee_pending (value : U64) (context : NativeTaskContext) :
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll
      ⟨⟨true, ⟨value⟩⟩⟩ context = (do
        NativeWaker.wakeByRef context.waker
        Result.ok (.Pending, ⟨⟨false, ⟨value⟩⟩⟩, context)) := by
  simp [effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok]

theorem callee_ready (value : U64) (context : NativeTaskContext) :
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll
      ⟨⟨false, ⟨value⟩⟩⟩ context =
        Result.ok (.Ready (core.num.U64.saturating_add value 1#u64),
          ⟨⟨false, ⟨value⟩⟩⟩, context) := by
  simp [effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    effects_core.saturating_increment, core.pin.PinMutAT.get_mut, NativeM.ok]

/-- The actual Rust caller, including both polls and its cancellation branch. -/
theorem driver_contract (value : U64) (cancel : Bool) (context : NativeTaskContext) :
    drive_paused_counter value cancel context = (do
      NativeWaker.wakeByRef context.waker
      Result.ok (if cancel then none else some (core.num.U64.saturating_add value 1#u64), context)) := by
  cases cancel <;>
    simp [drive_paused_counter, effects_core.paused_counter, callee_pending, callee_ready,
      NativeM.ok, bind_assoc]

theorem driver_next {α : Type} (value : U64) (cancel : Bool) (context : NativeTaskContext)
    (next : (Option U64 × NativeTaskContext) → NativeM α) (env : Environment)
    (bounded : context.waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == context.waker.id) =
      [(context.waker.id, NativeWaker.typeName, .atom "idle")]) :
    (drive_paused_counter value cancel context >>= next) env =
      next (if cancel then none else some (core.num.U64.saturating_add value 1#u64), context)
        (NativeWaker.notifiedEnv context.waker env) := by
  rw [driver_contract]
  simp only [bind_assoc, Result.ok_bind]
  exact NativeWaker.wakeByRef_registered_next context.waker _ env bounded stored

theorem completion (value : U64) (context : NativeTaskContext) (env : Environment)
    (bounded : context.waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == context.waker.id) =
      [(context.waker.id, NativeWaker.typeName, .atom "idle")]) :
    ∃ result,
      drive_paused_counter value false context env =
        (.ok (some result, context), NativeWaker.notifiedEnv context.waker env) ∧
      result.val = min U64.max (value.val + 1) := by
  refine ⟨core.num.U64.saturating_add value 1#u64, ?_, ?_⟩
  · simpa using driver_next value false context Result.ok env bounded stored
  · simp

theorem cancellation (value : U64) (context : NativeTaskContext) (env : Environment)
    (bounded : context.waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == context.waker.id) =
      [(context.waker.id, NativeWaker.typeName, .atom "idle")]) :
    drive_paused_counter value true context env =
      (.ok (none, context), NativeWaker.notifiedEnv context.waker env) := by
  simpa using driver_next value true context Result.ok env bounded stored

theorem missing_callback (value : U64) (cancel : Bool) (context : NativeTaskContext)
    (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == context.waker.id) = []) :
    drive_paused_counter value cancel context env = (.error .exhausted, env) := by
  rw [driver_contract]
  exact NativeWaker.wakeByRef_missing_next context.waker _ env missing

end Driver.Properties
