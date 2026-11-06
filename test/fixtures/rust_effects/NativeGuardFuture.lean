module
public import GuardAwait.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace GuardAwait.Properties

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


@[expose] def initial (amount : U64) : guarded_suspending.closure :=
  ⟨⟨1⟩, amount, 0#u32, none, none, none, none⟩

@[expose] def retainedFuture (amount : U64) (changed : Bool)
    (guard : NativeGuard effects_core.Counter) : guarded_suspending.closure :=
  ⟨⟨1⟩, amount, 3#u32, some guard, some changed, some ⟨false, ⟨amount⟩⟩, some true⟩

@[expose] def completed (amount : U64) (changed : Bool) : guarded_suspending.closure :=
  ⟨⟨1⟩, amount, 1#u32, none, some changed, some ⟨false, ⟨amount⟩⟩, some false⟩

@[expose] def registered (env : Environment) (value : effects_core.Counter) (poisoned : Bool) : Environment :=
  { env with refCounter := 1, nativeHeap := [
    (1, NativeMutex.typeName effects_core.Counter,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value]),
    (0, NativeWaker.typeName, .atom "idle")] }

@[expose] def held (env : Environment) (value : effects_core.Counter) (poisoned : Bool) : Environment :=
  { env with refCounter := 2, nativeHeap := [
    (1, NativeMutex.typeName effects_core.Counter,
      NativeMutex.lockedContents env.currentPid 2 poisoned value),
    (0, NativeWaker.typeName, .atom "notified")] }

@[expose] def released (env : Environment) (value : effects_core.Counter) (poisoned : Bool) : Environment :=
  { env with refCounter := 2, nativeHeap := [
    (1, NativeMutex.typeName effects_core.Counter,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value]),
    (0, NativeWaker.typeName, .atom "notified")] }

@[expose] def guardFor (env : Environment) (value : effects_core.Counter) : NativeGuard effects_core.Counter :=
  ⟨⟨1⟩, 2, env.currentPid, value⟩

theorem initial_state (amount : U64) :
    guarded_suspending ⟨1⟩ amount = Result.ok (initial amount) := rfl

theorem drop_unstarted (amount : U64) :
    guarded_suspending.closure.drop_owned (initial amount) = Result.ok () := rfl

theorem completed_drop (amount : U64) (changed : Bool) :
    guarded_suspending.closure.drop_owned (completed amount changed) = Result.ok () := rfl

theorem first_pending_next {α : Type} (value updated : effects_core.Counter) (amount : U64)
    (changed poisoned : Bool) (env : Environment)
    (computed : effects_core.increment value amount = Result.ok (changed, updated))
    (next : (core.task.poll.Poll Bool × effects_native.core.pin.Pin guarded_suspending.closure × NativeTaskContext) → Result α) :
    (guarded_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0⟩⟩ >>= next) (registered env value poisoned) =
      next (.Pending, ⟨retainedFuture amount changed (guardFor env updated)⟩, ⟨⟨0⟩⟩) (held env value poisoned) := by
  have unfolded : guarded_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0⟩⟩ = (do
    let acquired ← NativeMutex.lock (α := effects_core.Counter) ⟨1⟩
    let guard ← effects_core.recover_guard acquired
    let (changed, updated) ← effects_core.increment_guard guard amount
    NativeWaker.wakeByRef ⟨0⟩
    Result.ok (.Pending, ⟨retainedFuture amount changed updated⟩, ⟨⟨0⟩⟩)) := by
    unfold guarded_suspending.closure.poll
    split <;> simp_all [initial, retainedFuture, effects_core.paused_counter,
      core.future.into_future.IntoFuture.Blanket.into_future,
      effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
      core.pin.PinMutAT.get_mut, NativeM.ok, bind_assoc] <;>
        simp_all [UScalar.ofNatCore, UScalar.val]
  rw [unfolded]
  let start := registered env value poisoned
  let acquired : Environment := {start with refCounter := 2, nativeHeap := [(1, NativeMutex.typeName effects_core.Counter,
      NativeMutex.lockedContents env.currentPid 2 poisoned value),
      (0, NativeWaker.typeName, .atom "idle")] }
  have ready : NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩ start = some (.ok
      (if poisoned then .Err ⟨guardFor env value⟩ else .Ok (guardFor env value)), acquired) := by
    simpa [start, acquired, registered, guardFor] using
      NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex effects_core.Counter) value poisoned start
        (by simp [start, registered]) (by simp [start, registered])
  rw [NativeMutex.lock, Result.wait_bind, Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  have recovered : effects_core.recover_guard
      (if poisoned then .Err ⟨guardFor env value⟩ else .Ok (guardFor env value)) =
        Result.ok (guardFor env value) := by cases poisoned <;> rfl
  simp only [Result.ok_bind, recovered]
  rw [callee_contract]
  simp only [guardFor, computed, NativeM.ok, Result.ok_bind]
  have wakeReady : NativeWaker.pollWake ⟨0⟩ acquired = some (.ok (), held env value poisoned) := by
    simp [NativeWaker.pollWake, acquired, start, registered, held]
  simp only [NativeWaker.wakeByRef, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ wakeReady]
  simp

theorem cancel_pending_next {α : Type} (value updated : effects_core.Counter) (amount : U64)
    (changed poisoned : Bool) (env : Environment) (next : Result α) :
    (do guarded_suspending.closure.drop_owned (retainedFuture amount changed (guardFor env updated)); next)
      (held env value poisoned) = next (released env updated poisoned) := by
  have unfolded : guarded_suspending.closure.drop_owned (retainedFuture amount changed (guardFor env updated)) =
      NativeGuard.release (guardFor env updated) := by rfl
  rw [unfolded]
  simpa [held, released, guardFor] using NativeGuard.release_owned_next
    (guardFor env updated) value poisoned next (held env value poisoned) rfl (by simp [held, guardFor])

theorem cancel_pending (value updated : effects_core.Counter) (amount : U64)
    (changed poisoned : Bool) (env : Environment) :
    guarded_suspending.closure.drop_owned (retainedFuture amount changed (guardFor env updated))
      (held env value poisoned) = (.ok (), released env updated poisoned) := by
  have unfolded : guarded_suspending.closure.drop_owned (retainedFuture amount changed (guardFor env updated)) =
      NativeGuard.release (guardFor env updated) := by rfl
  rw [unfolded]
  simpa [held, released, guardFor] using NativeGuard.release_owned
    (guardFor env updated) value poisoned (held env value poisoned) rfl (by simp [held, guardFor])

theorem first_pending (value : effects_core.Counter) (amount : U64) (poisoned : Bool) (env : Environment) :
    ∃ (changed : Bool) (updated : effects_core.Counter),
      guarded_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0⟩⟩ (registered env value poisoned) =
        (.ok (.Pending, ⟨retainedFuture amount changed (guardFor env updated)⟩, ⟨⟨0⟩⟩), held env value poisoned) ∧
      (if changed then updated.value.val = value.value.val + amount.val
        else updated = value ∧ U64.max < value.value.val + amount.val) := by
  obtain ⟨changed, updated, computed, property⟩ := increment_spec value amount
  refine ⟨changed, updated, ?_, property⟩
  simpa using first_pending_next value updated amount changed poisoned env computed Result.ok

/-- The actual destructor commits the guard's mutated view, including cancellation. -/
theorem suspend_then_cancel (value : effects_core.Counter) (amount : U64) (poisoned : Bool) (env : Environment) :
    ∃ (changed : Bool) (updated : effects_core.Counter),
      (do
        let future ← guarded_suspending ⟨1⟩ amount
        let (_, future, _) ← guarded_suspending.closure.poll ⟨future⟩ ⟨⟨0⟩⟩
        guarded_suspending.closure.drop_owned future.pointer) (registered env value poisoned) =
          (.ok (), released env updated poisoned) ∧
      (if changed then updated.value.val = value.value.val + amount.val
        else updated = value ∧ U64.max < value.value.val + amount.val) := by
  obtain ⟨changed, updated, computed, property⟩ := increment_spec value amount
  refine ⟨changed, updated, ?_, property⟩
  have composed := first_pending_next value updated amount changed poisoned env computed
    (fun output => guarded_suspending.closure.drop_owned output.2.1.pointer)
  simpa [guarded_suspending, NativeM.ok, initial, cancel_pending] using composed

theorem resume_contract (amount : U64) (changed : Bool) (guard : NativeGuard effects_core.Counter) :
    guarded_suspending.closure.poll ⟨retainedFuture amount changed guard⟩ ⟨⟨0⟩⟩ = (do
      NativeGuard.release guard
      Result.ok (.Ready changed, ⟨completed amount changed⟩, ⟨⟨0⟩⟩)) := by
  unfold guarded_suspending.closure.poll
  split <;> simp_all [retainedFuture, completed,
    effects_core.PausedCounter.Insts.CoreFutureFutureFutureU64.poll,
    effects_core.saturating_increment, core.pin.PinMutAT.get_mut, effects_core.release_guard,
    NativeDrop.drop, NativeM.ok] <;>
      simp_all [UScalar.ofNatCore, UScalar.val]

theorem resume_next {α : Type} (value updated : effects_core.Counter) (amount : U64)
    (changed poisoned : Bool) (env : Environment)
    (next : (core.task.poll.Poll Bool × effects_native.core.pin.Pin guarded_suspending.closure × NativeTaskContext) → Result α) :
    (guarded_suspending.closure.poll ⟨retainedFuture amount changed (guardFor env updated)⟩ ⟨⟨0⟩⟩ >>= next)
      (held env value poisoned) = next (.Ready changed, ⟨completed amount changed⟩, ⟨⟨0⟩⟩) (released env updated poisoned) := by
  have dropContract : guarded_suspending.closure.drop_owned (retainedFuture amount changed (guardFor env updated)) =
      NativeGuard.release (guardFor env updated) := by rfl
  rw [resume_contract]
  simpa only [dropContract, bind_assoc, Result.ok_bind] using
    cancel_pending_next value updated amount changed poisoned env
      (next (.Ready changed, ⟨completed amount changed⟩, ⟨⟨0⟩⟩))

theorem two_polls (value : effects_core.Counter) (amount : U64) (poisoned : Bool) (env : Environment) :
    ∃ (changed : Bool) (updated : effects_core.Counter),
      (do
        let future ← guarded_suspending ⟨1⟩ amount
        let (first, future, context) ← guarded_suspending.closure.poll ⟨future⟩ ⟨⟨0⟩⟩
        let (second, finalState, _) ← guarded_suspending.closure.poll future context
        Result.ok (first, second, finalState)) (registered env value poisoned) =
          (.ok (.Pending, .Ready changed, ⟨completed amount changed⟩), released env updated poisoned) ∧
      (if changed then updated.value.val = value.value.val + amount.val
        else updated = value ∧ U64.max < value.value.val + amount.val) := by
  obtain ⟨changed, updated, computed, property⟩ := increment_spec value amount
  refine ⟨changed, updated, ?_, property⟩
  have composed := first_pending_next value updated amount changed poisoned env computed
    (fun output => do
      let (first, future, context) := output
      let (second, finalState, _) ← guarded_suspending.closure.poll future context
      Result.ok (first, second, finalState))
  have resumed := resume_next value updated amount changed poisoned env
    (fun output => Result.ok ((core.task.poll.Poll.Pending : core.task.poll.Poll Bool), output.1, output.2.1))
  simpa [guarded_suspending, NativeM.ok, initial, resumed] using composed

/-- Another execution context cannot acquire the mutex while this future is Pending. -/
private theorem held_contends (value : effects_core.Counter) (poisoned : Bool) (env : Environment)
    (other : PID) (different : env.currentPid ≠ other) :
    NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩ {held env value poisoned with currentPid := other} = none := by
  cases poisoned <;> simp [NativeMutex.pollLock, held, NativeMutex.lockedContents,
    NativeCodec.roundtrip, different]

/-- The actual Rust Pending result keeps other execution contexts blocked. -/
theorem pending_contends (value : effects_core.Counter) (amount : U64) (poisoned : Bool)
    (env : Environment) (other : PID) (different : env.currentPid ≠ other) :
    ∃ (changed : Bool) (updated : effects_core.Counter),
      guarded_suspending.closure.poll ⟨initial amount⟩ ⟨⟨0⟩⟩ (registered env value poisoned) =
        (.ok (.Pending, ⟨retainedFuture amount changed (guardFor env updated)⟩, ⟨⟨0⟩⟩), held env value poisoned) ∧
      NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩
        {held env value poisoned with currentPid := other} = none := by
  obtain ⟨changed, updated, pending, _⟩ := first_pending value amount poisoned env
  exact ⟨changed, updated, pending, held_contends value poisoned env other different⟩

theorem stale_guard_exhausts (value updated : effects_core.Counter) (amount : U64)
    (changed poisoned : Bool) (env : Environment) :
    guarded_suspending.closure.drop_owned
      (retainedFuture amount changed {guardFor env updated with token := 3})
      (held env value poisoned) = (.error .exhausted, held env value poisoned) := by
  have unfolded : guarded_suspending.closure.drop_owned
      (retainedFuture amount changed {guardFor env updated with token := 3}) =
      NativeGuard.release {guardFor env updated with token := 3} := by rfl
  rw [unfolded]
  have invalid : NativeGuard.pollRelease {guardFor env updated with token := 3}
      (held env value poisoned) = some (.error .exhausted, held env value poisoned) := by
    cases poisoned <;> simp [NativeGuard.pollRelease, held, guardFor, NativeMutex.lockedContents]
  rw [NativeGuard.release, Result.wait_ready_apply _ _ _ _ _ invalid]
  simp

theorem repoll_completed (amount : U64) (changed : Bool) :
    guarded_suspending.closure.poll ⟨completed amount changed⟩ ⟨⟨0⟩⟩ =
      Result.error (.error (.atom "rust_panicked")) := rfl

end GuardAwait.Properties
