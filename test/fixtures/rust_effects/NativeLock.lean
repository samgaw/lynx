module
public import Runtime.Lock.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.LockProperties

/-- The contract is proved over the actual extracted first-party callee. -/
theorem callee_contract (mutex : NativeMutex effects_core.Counter) :
    effects_core.acquire_counter mutex = NativeMutex.lock mutex := rfl

/-- A normal or poisoned acquisition owns the token and preserves unrelated cells. -/
theorem acquired (mutex : NativeMutex effects_core.Counter) (value : effects_core.Counter)
    (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    effects_core.acquire_counter mutex env = (.ok (
      if poisoned then .Err ⟨⟨mutex, env.nativeRefCounter + 1, env.currentPid, value⟩⟩
      else .Ok ⟨mutex, env.nativeRefCounter + 1, env.currentPid, value⟩),
      { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, NativeMutex.typeName effects_core.Counter,
            NativeMutex.lockedContents env.currentPid (env.nativeRefCounter + 1) poisoned value)
          else cell }) := by
  simpa [callee_contract] using NativeMutex.lock_unlocked mutex value poisoned env stored fresh

/-- The native-crate caller composes the verified contract in another crate. -/
theorem composed_acquisition (mutex : NativeMutex effects_core.Counter) :
    mutex_acquire mutex = NativeMutex.lock mutex := by
  change effects_core.acquire_counter mutex = NativeMutex.lock mutex
  exact callee_contract mutex

/-- Another context's guard makes acquisition wait rather than return a guard. -/
theorem contention_waits (mutex : NativeMutex effects_core.Counter) (value : effects_core.Counter)
    (owner : PID) (token : Nat) (poisoned : Bool) (env : Environment)
    (different : owner ≠ env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents owner token poisoned value)]) :
    effects_core.acquire_counter mutex = Result.wait (NativeMutex.pollLock mutex)
      (fun reply => match reply with | .ok result => .ok result | .error error => .error error) ∧
      NativeMutex.pollLock mutex env = none := by
  constructor
  · simp [callee_contract, NativeMutex.lock]
    funext reply
    cases reply <;> rfl
  · cases poisoned <;> simp [NativeMutex.pollLock, NativeMutex.lockedContents, stored, different]

/-- Recursive acquisition is an unsupported cutoff, not a successful return. -/
theorem recursive_cutoff (mutex : NativeMutex effects_core.Counter) (value : effects_core.Counter)
    (token : Nat) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents env.currentPid token poisoned value)]) :
    effects_core.acquire_counter mutex env = (.error .exhausted, env) := by
  rw [callee_contract]
  unfold NativeMutex.lock
  have ready : NativeMutex.pollLock mutex env = some (.error .exhausted, env) := by
    cases poisoned <;> simp [NativeMutex.pollLock, NativeMutex.lockedContents, stored]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- A missing identity is never accepted as a valid Rust mutex argument. -/
theorem missing_cutoff (mutex : NativeMutex effects_core.Counter) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) = []) :
    effects_core.acquire_counter mutex env = (.error .exhausted, env) := by
  rw [callee_contract]
  unfold NativeMutex.lock
  have ready : NativeMutex.pollLock mutex env = some (.error .exhausted, env) := by
    simp [NativeMutex.pollLock, missing]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

end Runtime.LockProperties
