module
public import Cancel.Extraction.Funs
public section
open Aeneas Aeneas.Std effects_native Lynx
namespace Cancel.Properties

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
    (env : Environment) (bounded : waker.id ≤ env.nativeRefCounter)
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

@[expose] def initial (value : U64) : owned_suspending.closure :=
  ⟨value, 0#u32, none, none, none⟩

@[expose] def pending (value : U64) : owned_suspending.closure :=
  ⟨value, 3#u32, some ⟨1⟩, some ⟨false, ⟨value⟩⟩, some true⟩

@[expose] def completed (value : U64) : owned_suspending.closure :=
  ⟨value, 1#u32, none, some ⟨false, ⟨value⟩⟩, some false⟩

@[expose] def registered (env : Environment) : Environment :=
  {env with nativeRefCounter := 0, nativeHeap := [(0, NativeWaker.typeName, .atom "idle")]}

@[expose] def retained (env : Environment) (value : U64) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [
    (1, NativeMutex.typeName U64, .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value]),
    (0, NativeWaker.typeName, .atom "notified")]}

@[expose] def reclaimed (env : Environment) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(0, NativeWaker.typeName, .atom "notified")]}

theorem initial_state (value : U64) :
    owned_suspending value = Result.ok (initial value) := rfl

theorem drop_unstarted (value : U64) :
    owned_suspending.closure.drop_owned (initial value) = Result.ok () := rfl

theorem drop_invalid_tag (value : U64) :
    owned_suspending.closure.drop_owned ⟨value, 4#u32, none, none, none⟩ =
      Result.error .exhausted := rfl

theorem drop_missing_owner (value : U64) :
    owned_suspending.closure.drop_owned ⟨value, 3#u32, none, none, none⟩ =
      Result.error .exhausted := rfl

theorem first_pending_next {α : Type} (value : U64) (env : Environment)
    (next : (core.task.poll.Poll U64 × effects_native.core.pin.Pin owned_suspending.closure × NativeTaskContext) → Result α) :
    (owned_suspending.closure.poll ⟨initial value⟩ ⟨⟨0, false⟩⟩ >>= next) (registered env) =
      next (.Pending, ⟨pending value⟩, ⟨⟨0, false⟩⟩) (retained env value) := by
  have unfolded : owned_suspending.closure.poll ⟨initial value⟩ ⟨⟨0, false⟩⟩ = (do
    let mutex ← NativeMutex.new value
    NativeWaker.wakeByRef ⟨0, false⟩
    Result.ok (.Pending, ⟨⟨value, 3#u32, some mutex, some ⟨false, ⟨value⟩⟩, some true⟩⟩, ⟨⟨0, false⟩⟩)) := by
      unfold owned_suspending.closure.poll
      split <;> simp_all [initial, effects_core.paused_counter,
        core.future.into_future.IntoFuture.Blanket.into_future,
        effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
        core.pin.PinMutAT.get_mut, NativeM.ok, bind_assoc] <;> simp_all [UScalar.ofNatCore, UScalar.val]
  rw [unfolded]
  simp [NativeMutex.new, NativeM.allocate, registered, bind_assoc]
  let allocated : Environment := { env with nativeRefCounter := 1, nativeHeap := [
    (1, NativeMutex.typeName U64, .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value]),
    (0, NativeWaker.typeName, .atom "idle")] }
  have ready : NativeWaker.pollWake ⟨0, false⟩ allocated = some (.ok (), retained env value) := by
    simp [NativeWaker.pollWake, allocated, retained]
  simp only [NativeWaker.wakeByRef, Bool.false_eq_true, ↓reduceIte]
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp [pending]

theorem first_pending (value : U64) (env : Environment) :
    owned_suspending.closure.poll ⟨initial value⟩ ⟨⟨0, false⟩⟩ (registered env) =
      (.ok (.Pending, ⟨pending value⟩, ⟨⟨0, false⟩⟩), retained env value) := by
  simpa using first_pending_next value env Result.ok

theorem cancel_pending (value : U64) (env : Environment) :
    owned_suspending.closure.drop_owned (pending value) (retained env value) =
      (.ok (), reclaimed env) := by
  have unfolded : owned_suspending.closure.drop_owned (pending value) =
      NativeMutex.dispose (α := U64) ⟨1⟩ := by rfl
  rw [unfolded]
  simp [retained, reclaimed, NativeMutex.dispose, NativeM.readCell, NativeM.removeCell,
    NativeCodec.roundtrip]

theorem completed_drop (value : U64) :
    owned_suspending.closure.drop_owned (completed value) = Result.ok () := rfl

/-- Compose actual construction, suspension and compiler destruction. -/
theorem suspend_then_cancel (value : U64) (env : Environment) :
    (do
      let future ← owned_suspending value
      let (_, future, _) ← owned_suspending.closure.poll ⟨future⟩ ⟨⟨0, false⟩⟩
      owned_suspending.closure.drop_owned future.pointer) (registered env) =
        (.ok (), reclaimed env) := by
  have composed := first_pending_next value env
    (fun output => owned_suspending.closure.drop_owned output.2.1.pointer)
  simpa [owned_suspending, NativeM.ok, initial, cancel_pending] using composed

theorem resume_ready (value : U64) (env : Environment) :
    ∃ result, owned_suspending.closure.poll ⟨pending value⟩ ⟨⟨0, false⟩⟩ (retained env value) =
      (.ok (.Ready result, ⟨completed value⟩, ⟨⟨0, false⟩⟩), reclaimed env) ∧
      result.val = min U64.max (value.val + 1) := by
  have unfolded : owned_suspending.closure.poll ⟨pending value⟩ ⟨⟨0, false⟩⟩ = (do
    let result ← effects_core.saturating_increment value
    NativeMutex.dispose (α := U64) ⟨1⟩
    Result.ok (.Ready result, ⟨completed value⟩, ⟨⟨0, false⟩⟩)) := by
    unfold owned_suspending.closure.poll
    split <;> simp_all [pending, completed,
      effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
      core.pin.PinMutAT.get_mut, core.mem.replace, NativeDrop.drop, NativeM.ok,
      bind_assoc] <;> simp_all [UScalar.ofNatCore, UScalar.val]
  obtain ⟨result, computed, arithmetic⟩ := core_increment value
  refine ⟨result, ?_, arithmetic⟩
  rw [unfolded, computed]
  simp [retained, reclaimed, NativeMutex.dispose, NativeM.readCell, NativeM.removeCell,
    NativeCodec.roundtrip]

end Cancel.Properties
