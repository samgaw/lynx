module
public import LockedFileResource.Model
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace LockedFileResource.Properties
open NativeFile

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeFile.typeName NativeFile.closedTypeName List.filter

theorem construct_next {α : Type} (state : State) (env : Environment)
    (next : NativeResourceArc effects_native.LockedFileResource → NativeM α)
    (registered : NativeResourceArc.typeName effects_native.LockedFileResource ∈ env.nativeResourceTypes) :
    (locked_file_resource_new ⟨1⟩ >>= next) (initial env state) = next ⟨3,4⟩ (live env state) := by
  simp [locked_file_resource_new, NativeMutex.new, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeM.allocate, initial, live, fileCell, mutexCell, payload, registered, bind_assoc]

/-- Releasing the final Rust owner invokes the extracted payload destructor,
consumes its file capability and retains the disk image after Arc reclamation. -/
theorem final_release_next {α : Type} (before after : State) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) (next : Unit → NativeM α) :
    (locked_file_resource_release ⟨3,4⟩ >>= next) (live env before) = next () (retired env after) := by
  let closingEnv := NativeResourceArc.retiredState (⟨3,4⟩ : NativeResourceArc effects_native.LockedFileResource) (live env before)
  have cleanup : ∀ next : NativeM α,
      (do NativeResourceCleanup.cleanup payload; next) closingEnv =
        next (retired env after) := by
    intro next
    have poll : pollClose ⟨1⟩ closingEnv =
        some (.ok (), retire ⟨1⟩ after closingEnv) := by
      simp [closingEnv, NativeResourceArc.retiredState, pollClose, lookup, live, mutexCell, fileCell, decode_valid before valid, ready, step]
    have h := cleanup_ready payload ⟨1⟩ false closingEnv
      (retire ⟨1⟩ after closingEnv)
      (by simp [closingEnv, NativeResourceArc.retiredState, payload, live, mutexCell, fileCell]) poll
      (by simp [closingEnv, NativeResourceArc.retiredState, payload, retire, live, mutexCell, fileCell]) (fun _ => next)
    simpa [closingEnv, NativeResourceArc.retiredState, retired, NativeResourceCleanup.cleanup, retire, live, cleaned, fileCell, mutexCell,
      closedCell, payload] using h
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨3,4⟩ : NativeResourceArc effects_native.LockedFileResource) payload next (live env before) (retired env after)
    (.inr policy)
    (by simp [live, mutexCell, fileCell]) (by simp [live, mutexCell, fileCell])
    (by simp [live, mutexCell, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType]) cleanup

  simpa [locked_file_resource_release, monadLift_self, NativeOwnedDrop.drop, cleaned, retired, closedCell]
    using released

@[expose] def aliased (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 5, nativeHeap := [
    (5, NativeResourceArc.handleType effects_native.LockedFileResource, .nativeReference 3),
    (4, NativeResourceArc.handleType effects_native.LockedFileResource, .nativeReference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 2, NativeCodec.encode payload]), mutexCell, fileCell state]}

@[expose] def retained (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 5, nativeHeap := [
    (5, NativeResourceArc.handleType effects_native.LockedFileResource, .nativeReference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), mutexCell, fileCell state]}

theorem clone_next {α : Type} (state : State) (env : Environment)
    (next : NativeResourceArc effects_native.LockedFileResource → NativeM α) :
    (locked_file_resource_clone ⟨3,4⟩ >>= next) (live env state) = next ⟨3,5⟩ (aliased env state) := by
  have cloned := NativeResourceArc.clone_single_next
    (⟨3,4⟩ : NativeResourceArc effects_native.LockedFileResource) payload next (live env state)
    (by simp [live, mutexCell, fileCell]) (by simp [live, mutexCell, fileCell])
    (by simp [live, mutexCell, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
    (by simp [live, mutexCell, fileCell])
  simpa [locked_file_resource_clone, monadLift_self, live, aliased, mutexCell, fileCell, List.map] using cloned

/-- A retained alias prevents file destruction, including when its close script
is blocked or absent. No close outcome is consumed by this release. -/
theorem retained_release_next {α : Type} (state : State) (env : Environment)
    (next : Unit → NativeM α) :
    (locked_file_resource_release ⟨3,4⟩ >>= next) (aliased env state) = next () (retained env state) := by
  have released := NativeResourceArc.releaseOwned_retained_run_next
    (⟨3,4⟩ : NativeResourceArc effects_native.LockedFileResource) payload next (aliased env state)
    (by simp [aliased, mutexCell, fileCell]) (by simp [aliased, mutexCell, fileCell])
    (by simp [aliased, mutexCell, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
  simpa [locked_file_resource_release, monadLift_self, NativeOwnedDrop.drop, retained, aliased, mutexCell, fileCell,
    List.filter, List.map] using released

@[expose] def retainedCleaned (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 5, nativeHeap := [
    (5, NativeResourceArc.handleType effects_native.LockedFileResource, .nativeReference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), closedCell state]}

theorem retained_final_release_next {α : Type} (before after : State) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) (next : Unit → NativeM α) :
    (locked_file_resource_release ⟨3,5⟩ >>= next) (retained env before) = next () (retired env after 5) := by
  let closingEnv := NativeResourceArc.retiredState (⟨3,5⟩ : NativeResourceArc effects_native.LockedFileResource) (retained env before)
  have cleanup : ∀ next : NativeM α,
      (do NativeResourceCleanup.cleanup payload; next) closingEnv =
        next (retired env after 5) := by
    intro next
    have poll : pollClose ⟨1⟩ closingEnv =
        some (.ok (), retire ⟨1⟩ after closingEnv) := by
      simp [closingEnv, NativeResourceArc.retiredState, pollClose, lookup, retained, mutexCell, fileCell, decode_valid before valid, ready, step]
    have h := cleanup_ready payload ⟨1⟩ false closingEnv
      (retire ⟨1⟩ after closingEnv)
      (by simp [closingEnv, NativeResourceArc.retiredState, payload, retained, mutexCell, fileCell]) poll
      (by simp [closingEnv, NativeResourceArc.retiredState, payload, retire, retained, mutexCell, fileCell]) (fun _ => next)
    simpa [closingEnv, NativeResourceArc.retiredState, retired, NativeResourceCleanup.cleanup, retire, retained, retainedCleaned, fileCell, mutexCell,
      closedCell, payload] using h
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨3,5⟩ : NativeResourceArc effects_native.LockedFileResource) payload next
    (retained env before) (retired env after 5)
    (.inr policy)
    (by simp [retained, mutexCell, fileCell]) (by simp [retained, mutexCell, fileCell])
    (by simp [retained, mutexCell, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType]) cleanup

  simpa [locked_file_resource_release, monadLift_self, NativeOwnedDrop.drop, retainedCleaned, retired, closedCell]
    using released

/-- Actual construction, aliasing and both releases close exactly on the last
owner. The ghost disk state survives resource reclamation. -/
theorem complete_cycle (before after : State) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous)
    (registered : NativeResourceArc.typeName effects_native.LockedFileResource ∈ env.nativeResourceTypes)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) :
    locked_file_resource_cycle ⟨1⟩ (initial env before) = (.ok (), retired env after 5) := by
  simp only [locked_file_resource_cycle, monadLift_self]
  have constructed := construct_next before env (fun first => do
    let second ← locked_file_resource_clone first
    locked_file_resource_release first
    locked_file_resource_release second) registered
  have cloned := clone_next before env (fun second => do
    locked_file_resource_release ⟨3,4⟩
    locked_file_resource_release second)
  have released := retained_release_next before env (fun _ => locked_file_resource_release ⟨3,5⟩)
  dsimp only at constructed cloned released
  rw [constructed, cloned, released]
  simpa [NativeM.ok] using retained_final_release_next before after env policy valid ready step Result.ok

@[expose] def held (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 5, nativeHeap := [
    (4, NativeResourceArc.handleType effects_native.LockedFileResource, .nativeReference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]),
    (2, NativeMutex.typeName NativeFile, NativeMutex.lockedContents env.currentPid 5 false (⟨1⟩ : NativeFile)),
    fileCell state]}

theorem sync_ready_next {α : Type} (before after : State) (env : Environment)
    (valid : Valid before) (ready : blocked before = false)
    (reply : core.result.Result Unit NativeIoError)
    (step : syncStep before = some (reply, after))
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (locked_file_resource_sync ⟨3,4⟩ >>= next) (live env before) =
      next reply {live env after with nativeRefCounter := 5} := by
  simp only [locked_file_resource_sync, monadLift_self, bind_assoc]
  simp only [NativeResourceArc.deref_single_next
    (⟨3,4⟩ : NativeResourceArc effects_native.LockedFileResource) payload _ (live env before)
    (by simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,live, mutexCell, fileCell]) (by simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,live, mutexCell, fileCell])
    (by simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,live, mutexCell, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])]
  have locking := NativeMutex.pollLock_unlocked (⟨2⟩ : NativeMutex NativeFile) ⟨1⟩ false
    (live env before) (by simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,live, mutexCell, fileCell, NativeCodec.encode])
    (by simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,live, mutexCell, fileCell])
  simp only [payload, NativeMutex.lock, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ locking]
  simp only [Bool.false_eq_true, if_false, NativeM.ok, Result.ok_bind, bind_assoc]
  have environment :
      ({live env before with
        nativeRefCounter := (live env before).nativeRefCounter + 1
        nativeHeap := (live env before).nativeHeap.map fun cell =>
        if cell.1 == 2 then (2, NativeMutex.typeName NativeFile,
          NativeMutex.lockedContents (live env before).currentPid ((live env before).nativeRefCounter + 1) false (⟨1⟩ : NativeFile))
        else cell} : Environment) = held env before := by
    simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,live, held, mutexCell, fileCell]
  rw [environment]
  simp only [NativeM.ok, Result.ok_bind, NativeGuard.deref,
    effects_core.synchronize_file, monadLift_self, syncAll, Result.wait_bind]
  have poll : pollSync ⟨1⟩ (held env before) = some (.ok reply, held env after) := by
    simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,pollSync, lookup, held, fileCell, decode_valid before valid, ready, step, store]
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp only [Result.ok_bind, NativeOwnedDrop.drop]
  have released := NativeGuard.release_owned_next
    (⟨⟨2⟩, 5, env.currentPid, ⟨1⟩⟩ : NativeGuard NativeFile)
    ⟨1⟩ false (next reply) (held env after) rfl
    (by simp [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,held, fileCell])
  simpa [NativeCodec.typeName,NativeMutex.typeName, NativeFile.typeName, NativeFile.closedTypeName,held, live, mutexCell, NativeCodec.encode, fileCell, bind_assoc] using released

@[expose] def closeChoice : Term :=
  .cons (.tuple #[.atom "close", .atom "ok", .integer 0, .bitstring ⟨#[0]⟩ 0]) .nil

/-- A full actual resource cycle does not convert close into fsync. The old
persistent byte remains a real admitted crash outcome after resource reclamation. -/
theorem cycle_keeps_disk (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous)
    (registered : NativeResourceArc.typeName effects_native.LockedFileResource ∈ env.nativeResourceTypes) :
    locked_file_resource_cycle ⟨1⟩ (initial env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, closeChoice⟩) =
      (.ok (), retired env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩ 5) ∧
    lookup ⟨1⟩ (retired env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩ 5) = none ∧
    crashImage ⟨1⟩ ⟨#[0]⟩ (retired env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩ 5) =
      some ⟨⟨#[1]⟩, 5⟩ := by
  refine ⟨complete_cycle _ _ env policy registered (by unfold Valid; decide)
    (by simp [NativeCodec.typeName,blocked, closeChoice])
    (by
      simp [NativeCodec.typeName,closeStep, action, closeChoice, persist, ← ByteArray.size_data]
      decide), ?_, ?_⟩
  · simp [NativeCodec.typeName,lookup, retired, closedCell, typeName, closedTypeName, handleTypeName, writableHandleTypeName, closedHandleTypeName]
  · simp [NativeCodec.typeName,crashImage, lookup, lookupClosed, retired, closedCell, typeName, closedTypeName, handleTypeName, writableHandleTypeName, closedHandleTypeName,
      decode, encode, limit, persist, ← ByteArray.size_data]
    decide

/-- Failed ResourceArc registration cleans up the already-created mutex and file. -/
theorem unregistered_cleanup (before after : State) (env : Environment)
    (absent : NativeResourceArc.typeName effects_native.LockedFileResource ∉ env.nativeResourceTypes)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) :
    locked_file_resource_new ⟨1⟩ (initial env before) =
      (.error (.error (.atom "rust_panicked")), retired env after 2) := by
  let wrapped : Environment := {env with nativeRefCounter := 2, nativeHeap := [mutexCell, fileCell before]}
  have poll : pollClose ⟨1⟩ wrapped = some (.ok (), retire ⟨1⟩ after wrapped) := by
    simp [pollClose, lookup, wrapped, mutexCell, fileCell, decode_valid before valid, ready, step]
  have cleanup := cleanup_ready payload ⟨1⟩ false wrapped (retire ⟨1⟩ after wrapped)
    (by simp [payload, wrapped, mutexCell, fileCell, NativeCodec.encode]) poll
    (by simp [payload, wrapped, retire, mutexCell, fileCell, NativeCodec.encode])
    (fun _ => (NativeM.fail .panic : NativeM (NativeResourceArc effects_native.LockedFileResource)))
  simpa [locked_file_resource_new, monadLift_self, NativeMutex.new, NativeM.allocate,
    NativeResourceArc.newOwned, absent, NativeResourceCleanup.cleanup, payload,
    NativeM.fail, retire, wrapped, initial, retired, fileCell, mutexCell, closedCell,
    NativeCodec.encode, List.filter] using cleanup

end LockedFileResource.Properties
