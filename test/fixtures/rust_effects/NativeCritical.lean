module
public import Runtime.Critical.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.CriticalProperties

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


/-- Both Result branches transfer the same complete guard, without releasing it. -/
theorem recover_success (guard : NativeGuard effects_core.Counter) :
    effects_core.recover_guard (.Ok guard) = Result.ok guard := rfl

theorem recover_poisoned (guard : NativeGuard effects_core.Counter) :
    effects_core.recover_guard (.Err ⟨guard⟩) = Result.ok guard := rfl

/-- The actual cross-crate caller composes recovery, checked mutation and release. -/
theorem critical_contract (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    locked_increment mutex amount = (do
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let (changed, updated) ← effects_core.increment guard.value amount
      NativeGuard.release { guard with value := updated }
      .ok changed) := by
  simp [locked_increment, effects_core.locked_increment, release_contract]

private def replaceCell (cells : List (Nat × String × Term)) (id : Nat)
    (cellName : String) (value : Term) : List (Nat × String × Term) :=
  cells.map fun cell => if cell.1 == id then (id, cellName, value) else cell

private theorem replacement_filter (cells : List (Nat × String × Term)) (id : Nat)
    (cellName : String) (old updated : Term)
    (stored : cells.filter (fun cell => cell.1 == id) = [(id, cellName, old)]) :
    (replaceCell cells id cellName updated).filter (fun cell => cell.1 == id) =
      [(id, cellName, updated)] := by
  unfold replaceCell
  rw [List.filter_map]
  have predicate : ((fun cell : Nat × String × Term => cell.1 == id) ∘
      (fun cell => if cell.1 == id then (id, cellName, updated) else cell)) =
      (fun cell => cell.1 == id) := by
    funext cell
    by_cases key : cell.1 = id <;> simp [key]
  rw [predicate, stored]
  simp

private theorem replacement_overwrite (cells : List (Nat × String × Term)) (id : Nat)
    (cellName : String) (first second : Term) :
    replaceCell (replaceCell cells id cellName first) id cellName second =
      replaceCell cells id cellName second := by
  simp only [replaceCell, List.map_map]
  congr 1
  funext cell
  by_cases key : cell.1 = id <;> simp [key]

/-- Complete acquisition/update/release preserves unrelated cells, commits the
latest value on success, and leaves the payload unchanged on overflow. Recovery
of a poisoned acquisition does not clear the existing poison status. -/
theorem critical_state (mutex : NativeMutex effects_core.Counter) (value : effects_core.Counter)
    (amount : U64) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    ∃ changed updated,
      locked_increment mutex amount env = (.ok changed, { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, NativeMutex.typeName effects_core.Counter, .tuple #[.atom "unlocked",
            .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode updated])
          else cell }) ∧
      (if changed then updated.value.val = value.value.val + amount.val
       else updated = value ∧ U64.max < value.value.val + amount.val) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec value amount
  refine ⟨changed, updated, ?_, property⟩
  let acquiredEnv : Environment := { env with
    nativeRefCounter := env.nativeRefCounter + 1
    nativeHeap := replaceCell env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
      (NativeMutex.lockedContents env.currentPid (env.nativeRefCounter + 1) poisoned value) }
  have held := replacement_filter env.nativeHeap mutex.id
    (NativeMutex.typeName effects_core.Counter) _
    (NativeMutex.lockedContents env.currentPid (env.nativeRefCounter + 1) poisoned value) stored
  have released := NativeGuard.release_owned_next
    (⟨mutex, env.nativeRefCounter + 1, env.currentPid, updated⟩ : NativeGuard effects_core.Counter)
    value poisoned (Result.ok changed) acquiredEnv rfl held
  have finalState : (do
      NativeGuard.release (⟨mutex, env.nativeRefCounter + 1, env.currentPid, updated⟩ : NativeGuard effects_core.Counter)
      Result.ok changed) acquiredEnv = (.ok changed, { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := replaceCell env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
          (.tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode updated]) }) := by
    simp only [Result.ok_apply] at released
    change _ = (Outcome.ok changed, { acquiredEnv with
      nativeHeap := replaceCell acquiredEnv.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
        (.tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode updated]) }) at released
    simpa only [acquiredEnv, replacement_overwrite] using released
  rw [critical_contract]
  unfold NativeMutex.lock
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _
    (NativeMutex.pollLock_unlocked mutex value poisoned env stored fresh)]
  cases poisoned <;>
    simpa [effects_core.recover_guard, NativePoisonError.into_inner, NativeM.ok, returned,
      acquiredEnv, replaceCell] using finalState




/-- A contending acquisition remains pending; this is not a totality claim. -/
theorem contention_waits (mutex : NativeMutex effects_core.Counter) (amount : U64)
    (value : effects_core.Counter) (owner : PID) (token : Nat) (poisoned : Bool) (env : Environment)
    (different : owner ≠ env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter,
        NativeMutex.lockedContents owner token poisoned value)]) :
    locked_increment mutex amount = (do
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let (changed, updated) ← effects_core.increment guard.value amount
      NativeGuard.release { guard with value := updated }
      Result.ok changed) ∧ NativeMutex.pollLock mutex env = none := by
  constructor
  · simpa [NativeM.ok] using critical_contract mutex amount
  · cases poisoned <;> simp [NativeMutex.pollLock, NativeMutex.lockedContents, stored, different]

/-- Missing native identities cannot count as successful critical sections. -/
theorem missing_cutoff (mutex : NativeMutex effects_core.Counter) (amount : U64) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) = []) :
    locked_increment mutex amount env = (.error .exhausted, env) := by
  have ready : NativeMutex.pollLock mutex env = some (.error .exhausted, env) := by
    simp [NativeMutex.pollLock, missing]
  rw [critical_contract]
  unfold NativeMutex.lock
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

end Runtime.CriticalProperties
