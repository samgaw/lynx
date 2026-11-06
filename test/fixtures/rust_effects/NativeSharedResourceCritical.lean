module
public import Shared.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Shared.Critical

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
  simp [effects_core.update_release, callee_contract, NativeOwnedDrop.drop, NativeM.ok,
    bind_assoc]


/-- Both Result branches transfer the same complete guard, without releasing it. -/
theorem recover_success (guard : NativeGuard effects_core.Counter) :
    effects_core.recover_guard (.Ok guard) = Result.ok guard := rfl

theorem recover_poisoned (guard : NativeGuard effects_core.Counter) :
    effects_core.recover_guard (.Err ⟨guard⟩) = Result.ok guard := rfl

/-- The actual cross-crate caller composes recovery, checked mutation and release. -/
theorem critical_contract (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    effects_core.locked_increment mutex amount = (do
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let (changed, updated) ← effects_core.increment guard.value amount
      NativeGuard.release { guard with value := updated }
      .ok changed) := by
  simp [effects_core.locked_increment, release_contract]

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
theorem critical_state_handled_next {α β : Type} (finish : Bool → NativeM α)
    (handler : Exception → NativeM α) (next : α → NativeM β) (mutex : NativeMutex effects_core.Counter) (value : effects_core.Counter)
    (amount : U64) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    ∃ changed updated,
      ((Result.handle (effects_core.locked_increment mutex amount >>= finish) handler) >>= next) env =
      ((Result.handle (finish changed) handler) >>= next) { env with
        refCounter := env.refCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, NativeMutex.typeName effects_core.Counter, .tuple #[.atom "unlocked",
            .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode updated])
          else cell } ∧
      (if changed then updated.value.val = value.value.val + amount.val
       else updated = value ∧ U64.max < value.value.val + amount.val) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec value amount
  refine ⟨changed, updated, ?_, property⟩
  let acquiredEnv : Environment := { env with
    refCounter := env.refCounter + 1
    nativeHeap := replaceCell env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
      (NativeMutex.lockedContents env.currentPid (env.refCounter + 1) poisoned value) }
  have held := replacement_filter env.nativeHeap mutex.id
    (NativeMutex.typeName effects_core.Counter) _
    (NativeMutex.lockedContents env.currentPid (env.refCounter + 1) poisoned value) stored
  have released := NativeGuard.release_owned_handled_next
    (⟨mutex, env.refCounter + 1, env.currentPid, updated⟩ : NativeGuard effects_core.Counter)
    value poisoned (finish changed) handler next acquiredEnv rfl held
  have finalState : ((Result.handle (do
      NativeGuard.release (⟨mutex, env.refCounter + 1, env.currentPid, updated⟩ : NativeGuard effects_core.Counter)
      finish changed) handler) >>= next) acquiredEnv =
        ((Result.handle (finish changed) handler) >>= next) { env with
        refCounter := env.refCounter + 1
        nativeHeap := replaceCell env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
          (.tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode updated]) } := by
    change _ = ((Result.handle (finish changed) handler) >>= next) { acquiredEnv with
      nativeHeap := replaceCell acquiredEnv.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
        (.tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode updated]) } at released
    simpa only [acquiredEnv, replacement_overwrite] using released
  rw [critical_contract]
  simp only [bind_assoc]
  unfold NativeMutex.lock
  simp only [Result.wait_bind, Result.handle]
  rw [Result.wait_ready_apply _ _ _ _ _
    (NativeMutex.pollLock_unlocked mutex value poisoned env stored fresh)]
  cases poisoned <;>
    simpa [effects_core.recover_guard, NativePoisonError.into_inner, NativeM.ok, returned,
      acquiredEnv, replaceCell, Result.handle] using finalState

theorem locked_read_handled_next {α β : Type} (finish : U64 → NativeM α)
    (handler : Exception → NativeM α) (next : α → NativeM β)
    (mutex : NativeMutex effects_core.Counter) (value : effects_core.Counter) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    ((Result.handle (do
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let observed ← effects_core.read_guard guard
      effects_core.release_guard guard
      finish observed) handler) >>= next) env =
      ((Result.handle (finish value.value) handler) >>= next) { env with
        refCounter := env.refCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, NativeMutex.typeName effects_core.Counter,
            .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value]) else cell} := by
  let heldEnv : Environment := { env with
    refCounter := env.refCounter + 1
    nativeHeap := replaceCell env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
      (NativeMutex.lockedContents env.currentPid (env.refCounter + 1) false value)}
  have held := replacement_filter env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter) _
    (NativeMutex.lockedContents env.currentPid (env.refCounter + 1) false value) stored
  have released := NativeGuard.release_owned_handled_next
    (⟨mutex, env.refCounter + 1, env.currentPid, value⟩ : NativeGuard effects_core.Counter)
    value false (finish value.value) handler next heldEnv rfl held
  have result : ((Result.handle (do
      NativeGuard.release (⟨mutex, env.refCounter + 1, env.currentPid, value⟩ : NativeGuard effects_core.Counter)
      finish value.value) handler) >>= next) heldEnv =
      ((Result.handle (finish value.value) handler) >>= next) { env with
        refCounter := env.refCounter + 1
        nativeHeap := replaceCell env.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
          (.tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])} := by
    change _ = ((Result.handle (finish value.value) handler) >>= next) { heldEnv with
      nativeHeap := replaceCell heldEnv.nativeHeap mutex.id (NativeMutex.typeName effects_core.Counter)
        (.tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value]) } at released
    simpa only [heldEnv, replacement_overwrite] using released
  unfold NativeMutex.lock
  simp only [Result.wait_bind, Result.handle]
  rw [Result.wait_ready_apply _ _ _ _ _
    (NativeMutex.pollLock_unlocked mutex value false env stored fresh)]
  simpa [effects_core.recover_guard, effects_core.read_guard, NativeGuard.deref,
    effects_core.release_guard, NativeOwnedDrop.drop, NativeM.ok, heldEnv, replaceCell, Result.handle] using result

end Shared.Critical
