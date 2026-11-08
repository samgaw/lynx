module
public import Runtime.Release.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.ReleaseProperties

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


/-- The actual owning callee releases the guard reconstructed by its mutable borrow. -/
theorem release_contract (guard : NativeGuard effects_core.Counter) (amount : U64) :
    effects_core.update_release guard amount = (do
      let (changed, updated) ← effects_core.increment guard.value amount
      NativeGuard.release { guard with value := updated }
      .ok changed) := by
  simp [effects_core.update_release, callee_contract, NativeDrop.drop, NativeM.ok,
    bind_assoc]

/-- The native-crate caller composes the proved implementation contract. -/
theorem composed_release (guard : NativeGuard effects_core.Counter) (amount : U64) :
    guard_update_release guard amount = (do
      let (changed, updated) ← effects_core.increment guard.value amount
      NativeGuard.release { guard with value := updated }
      .ok changed) := by
  change effects_core.update_release guard amount = _
  exact release_contract guard amount

/-- Both successful and rejected arithmetic release the lock, storing the latest
payload and retaining the existing poison state and every unrelated cell. -/
theorem update_release_state (guard : NativeGuard effects_core.Counter) (amount : U64)
    (original : effects_core.Counter) (poisoned : Bool) (env : Environment)
    (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    ∃ changed updated,
      guard_update_release guard amount env = (.ok changed,
        { env with nativeHeap := env.nativeHeap.map fun cell =>
          if cell.1 == guard.mutex.id then
            (guard.mutex.id, NativeMutex.typeName effects_core.Counter,
              .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
                NativeCodec.encode updated])
          else cell }) ∧
      (if changed then updated.value.val = guard.value.value.val + amount.val
       else updated = guard.value ∧ U64.max < guard.value.value.val + amount.val) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec guard.value amount
  refine ⟨changed, updated, ?_, property⟩
  have released := NativeGuard.release_owned_next { guard with value := updated }
    original poisoned (Result.ok changed) env owner stored
  simpa [composed_release, returned, NativeM.ok] using released

/-- Releasing without a write preserves the current payload. -/
theorem release_state (guard : NativeGuard effects_core.Counter) (poisoned : Bool)
    (env : Environment) (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned guard.value)]) :
    guard_release guard env = (.ok (), { env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName effects_core.Counter,
          .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
            NativeCodec.encode guard.value])
      else cell }) := by
  simpa [guard_release, effects_core.release_guard, NativeDrop.drop] using
    NativeGuard.release_owned guard guard.value poisoned env owner stored

/-- A panic after normal release does not poison an already released guard. -/
theorem panic_after_release (guard : NativeGuard effects_core.Counter) (accepted : Bool)
    (poisoned : Bool) (env : Environment) (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned guard.value)]) :
    guard_release_then_assert guard accepted env =
      (if accepted then .ok () else .error (.error (.atom "rust_panicked")),
        { env with nativeHeap := env.nativeHeap.map fun cell =>
          if cell.1 == guard.mutex.id then
            (guard.mutex.id, NativeMutex.typeName effects_core.Counter,
              .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
                NativeCodec.encode guard.value])
          else cell }) := by
  have released := NativeGuard.release_owned_next guard guard.value poisoned
    (NativeM.massert accepted) env owner stored
  cases accepted <;>
    simpa [guard_release_then_assert, NativeDrop.drop, NativeM.massert, NativeM.fail] using released


/-- The real caller uses the proved owning update before reacquiring the mutex. -/
theorem reacquire_contract (guard : NativeGuard effects_core.Counter) (amount : U64) :
    guard_update_reacquire guard guard.mutex amount = (do
      let (changed, updated) ← effects_core.increment guard.value amount
      NativeGuard.release { guard with value := updated }
      let acquired ← NativeMutex.lock guard.mutex
      .ok (changed, acquired)) := by
  simp [guard_update_reacquire, release_contract, effects_core.acquire_counter,
    NativeM.ok, bind_assoc]

/-- A subsequent actual Rust acquisition observes the latest committed payload,
with a fresh guard token. The initial lock belongs to the current context. -/
theorem reacquired_payload (guard : NativeGuard effects_core.Counter) (amount : U64)
    (original : effects_core.Counter) (env : Environment)
    (owner : guard.ownerContext = env.currentPid)
    (heap : env.nativeHeap = [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
      NativeMutex.lockedContents guard.ownerContext guard.token false original)])
    (fresh : env.nativeRefCounter + 1 ≠ guard.mutex.id) :
    ∃ changed updated,
      guard_update_reacquire guard guard.mutex amount env =
        (.ok (changed, .Ok ⟨guard.mutex, env.nativeRefCounter + 1, env.currentPid, updated⟩),
          { env with
            nativeRefCounter := env.nativeRefCounter + 1
            nativeHeap := [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
              NativeMutex.lockedContents env.currentPid (env.nativeRefCounter + 1) false updated)] }) ∧
      (if changed then updated.value.val = guard.value.value.val + amount.val
       else updated = guard.value ∧ U64.max < guard.value.value.val + amount.val) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec guard.value amount
  refine ⟨changed, updated, ?_, property⟩
  have stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents guard.ownerContext guard.token false original)] := by
    simp [heap]
  have released := NativeGuard.release_owned_next { guard with value := updated }
    original false (do
      let acquired ← NativeMutex.lock guard.mutex
      Result.ok (changed, acquired)) env owner stored
  simp only [heap, List.map_cons, List.map_nil, beq_self_eq_true, ↓reduceIte] at released
  simp only [reacquire_contract, returned, NativeM.ok, Result.ok_bind]
  rw [released]
  simp only [Bool.false_eq_true, ↓reduceIte]
  unfold NativeMutex.lock
  rw [Result.wait_bind]
  have ready := NativeMutex.pollLock_unlocked guard.mutex updated false
    { env with nativeHeap := [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
      .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode updated])] }
    (by simp) (by simp [Ne.symm fresh])
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp [NativeMutex.lockedContents]


private theorem rejected_release (guard : NativeGuard effects_core.Counter) (env : Environment)
    (invalid : NativeGuard.pollRelease guard env = some (.error .exhausted, env)) :
    guard_release guard env = (.error .exhausted, env) := by
  change NativeGuard.release guard env = _
  unfold NativeGuard.release
  rw [Result.wait_ready_apply _ _ _ _ _ invalid]
  simp

/-- Invalid handles cannot release a missing cell. -/
theorem missing_cutoff (guard : NativeGuard effects_core.Counter) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) = []) :
    guard_release guard env = (.error .exhausted, env) := by
  apply rejected_release
  simp [NativeGuard.pollRelease, missing]

/-- A guard cannot release a cell from another execution context. -/
theorem context_cutoff (guard : NativeGuard effects_core.Counter) (original : effects_core.Counter)
    (poisoned : Bool) (env : Environment) (different : guard.ownerContext ≠ env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    guard_release guard env = (.error .exhausted, env) := by
  apply rejected_release
  cases poisoned <;> simp [NativeGuard.pollRelease, NativeMutex.lockedContents, stored, different]

/-- Matching mutex identity is insufficient when the acquisition token differs. -/
theorem token_cutoff (guard : NativeGuard effects_core.Counter) (original : effects_core.Counter)
    (token : Nat) (poisoned : Bool) (env : Environment) (different : token ≠ guard.token)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents guard.ownerContext token poisoned original)]) :
    guard_release guard env = (.error .exhausted, env) := by
  apply rejected_release
  cases poisoned <;> simp [NativeGuard.pollRelease, NativeMutex.lockedContents, stored, different]


/-- Compiler-generated normal destruction commits exactly the same reconstructed
payload as the explicit owning release. This requires consuming drop lowering. -/
theorem scope_release_contract (guard : NativeGuard effects_core.Counter) (amount : U64) :
    guard_update_scope guard amount = guard_update_release guard amount := by
  rfl

end Runtime.ReleaseProperties
