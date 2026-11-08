module
public import FileResource.Model
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Properties
open NativeFile

theorem construct_next {α : Type} (state : State) (env : Environment)
    (next : NativeResourceArc effects_native.FileResource → NativeM α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (file_resource_new ⟨1⟩ >>= next) (initial env state) = next ⟨2,3⟩ (live env state) := by
  simp [file_resource_new, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeM.allocate, initial, live, fileCell, payload, registered, bind_assoc]

/-- Releasing the final Rust owner invokes the extracted payload destructor,
consumes its file capability and retains the disk image after Arc reclamation. -/
theorem final_release_next {α : Type} (before after : State) (env : Environment)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) (next : Unit → NativeM α) :
    (file_resource_release ⟨2,3⟩ >>= next) (live env before) = next () (retired env after) := by
  have cleanup : ∀ next : NativeM α,
      (do NativeResourceCleanup.cleanup payload; next) (live env before) =
        next (cleaned env after) := by
    intro next
    have h := cleanup_ready payload (live env before) before after
      (by simp [lookup, payload, live, fileCell, decode_valid before valid]) ready step (fun _ => next)
    simpa [NativeResourceCleanup.cleanup, retire, live, cleaned, fileCell, closedCell, payload] using h
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨2,3⟩ : NativeResourceArc effects_native.FileResource) payload next (live env before) (cleaned env after)
    (by simp [live, fileCell]) (by simp [live, fileCell])
    (by simp [live, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType]) cleanup
    (by simp [cleaned, closedCell]) (by simp [cleaned, closedCell])
    (by simp [cleaned, closedCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
  simpa [file_resource_release, monadLift_self, NativeOwnedDrop.drop, cleaned, retired, closedCell]
    using released

@[expose] def aliased (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType effects_native.FileResource, .nativeReference 2),
    (3, NativeResourceArc.handleType effects_native.FileResource, .nativeReference 2),
    (2, NativeResourceArc.typeName effects_native.FileResource,
      .tuple #[.integer 2, NativeCodec.encode payload]), fileCell state]}

@[expose] def retained (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType effects_native.FileResource, .nativeReference 2),
    (2, NativeResourceArc.typeName effects_native.FileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), fileCell state]}

theorem clone_next {α : Type} (state : State) (env : Environment)
    (next : NativeResourceArc effects_native.FileResource → NativeM α) :
    (file_resource_clone ⟨2,3⟩ >>= next) (live env state) = next ⟨2,4⟩ (aliased env state) := by
  have cloned := NativeResourceArc.clone_single_next
    (⟨2,3⟩ : NativeResourceArc effects_native.FileResource) payload next (live env state)
    (by simp [live, fileCell]) (by simp [live, fileCell])
    (by simp [live, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
    (by simp [live, fileCell])
  simpa [file_resource_clone, monadLift_self, live, aliased, fileCell, List.map] using cloned

/-- A retained alias prevents file destruction, including when its close script
is blocked or absent. No close outcome is consumed by this release. -/
theorem retained_release_next {α : Type} (state : State) (env : Environment)
    (next : Unit → NativeM α) :
    (file_resource_release ⟨2,3⟩ >>= next) (aliased env state) = next () (retained env state) := by
  have released := NativeResourceArc.releaseOwned_retained_run_next
    (⟨2,3⟩ : NativeResourceArc effects_native.FileResource) payload next (aliased env state)
    (by simp [aliased, fileCell]) (by simp [aliased, fileCell])
    (by simp [aliased, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
  simpa [file_resource_release, monadLift_self, NativeOwnedDrop.drop, retained, aliased, fileCell,
    List.filter, List.map] using released

@[expose] def retainedCleaned (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType effects_native.FileResource, .nativeReference 2),
    (2, NativeResourceArc.typeName effects_native.FileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), closedCell state]}

theorem retained_final_release_next {α : Type} (before after : State) (env : Environment)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) (next : Unit → NativeM α) :
    (file_resource_release ⟨2,4⟩ >>= next) (retained env before) = next () (retired env after 4) := by
  have cleanup : ∀ next : NativeM α,
      (do NativeResourceCleanup.cleanup payload; next) (retained env before) =
        next (retainedCleaned env after) := by
    intro next
    have h := cleanup_ready payload (retained env before) before after
      (by simp [lookup, payload, retained, fileCell, decode_valid before valid]) ready step (fun _ => next)
    simpa [NativeResourceCleanup.cleanup, retire, retained, retainedCleaned, fileCell, closedCell, payload] using h
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨2,4⟩ : NativeResourceArc effects_native.FileResource) payload next
    (retained env before) (retainedCleaned env after)
    (by simp [retained, fileCell]) (by simp [retained, fileCell])
    (by simp [retained, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType]) cleanup
    (by simp [retainedCleaned, closedCell]) (by simp [retainedCleaned, closedCell])
    (by simp [retainedCleaned, closedCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
  simpa [file_resource_release, monadLift_self, NativeOwnedDrop.drop, retainedCleaned, retired, closedCell]
    using released

/-- Actual construction, aliasing and both releases close exactly on the last
owner. The ghost disk state survives resource reclamation. -/
theorem complete_cycle (before after : State) (env : Environment)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) :
    file_resource_cycle ⟨1⟩ (initial env before) = (.ok (), retired env after 4) := by
  simp only [file_resource_cycle, monadLift_self]
  rw [construct_next before env _ registered]
  rw [clone_next before env]
  rw [retained_release_next before env]
  simpa [NativeM.ok] using retained_final_release_next before after env valid ready step Result.ok

/-- Synchronization follows the actual first-party call into the core crate. -/
theorem sync_contract (resource : NativeResourceArc effects_native.FileResource) :
    file_resource_sync resource = (do
      let value ← NativeResourceArc.deref resource
      effects_core.synchronize_file value.file) := rfl

/-- Missing registration still destroys the moved file before propagating panic. -/
theorem unregistered_cleanup (before after : State) (env : Environment)
    (absent : NativeResourceArc.typeName effects_native.FileResource ∉ env.nativeResourceTypes)
    (valid : Valid before) (ready : blocked before = false)
    (step : closeStep before = some after) :
    file_resource_new ⟨1⟩ (initial env before) =
      (.error (.error (.atom "rust_panicked")), retired env after 1) := by
  have cleanup := cleanup_ready payload (initial env before) before after
    (by simp [lookup, payload, initial, fileCell, decode_valid before valid]) ready step
    (fun _ => (NativeM.fail .panic : NativeM (NativeResourceArc effects_native.FileResource)))
  simpa [file_resource_new, monadLift_self, NativeResourceArc.newOwned, absent,
    NativeResourceCleanup.cleanup, payload, NativeM.fail, retire, initial, retired,
    fileCell, closedCell] using cleanup

theorem sync_ready_next {α : Type} (before after : State) (env : Environment)
    (valid : Valid before) (ready : blocked before = false)
    (reply : core.result.Result Unit NativeIoError)
    (step : syncStep before = some (reply, after))
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (file_resource_sync ⟨2,3⟩ >>= next) (live env before) = next reply (live env after) := by
  have observed := NativeResourceArc.deref_single_next
    (⟨2,3⟩ : NativeResourceArc effects_native.FileResource) payload
    (fun value => effects_core.synchronize_file value.file >>= next) (live env before)
    (by simp [live, fileCell]) (by simp [live, fileCell])
    (by simp [live, fileCell, encode, NativeResourceArc.typeName, NativeResourceArc.handleType])
  rw [sync_contract]
  simp only [bind_assoc]
  rw [observed]
  have poll : pollSync ⟨1⟩ (live env before) = some (.ok reply, live env after) := by
    simp [pollSync, lookup, live, fileCell, decode_valid before valid, ready, step, store]
  simp only [payload, effects_core.synchronize_file, monadLift_self, syncAll, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

@[expose] def closeChoice : Term :=
  .cons (.tuple #[.atom "close", .atom "ok", .integer 0, .bitstring ⟨#[0]⟩ 0]) .nil

/-- A full actual resource cycle does not convert close into fsync. The old
persistent byte remains a real admitted crash outcome after resource reclamation. -/
theorem cycle_keeps_disk (env : Environment)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    file_resource_cycle ⟨1⟩ (initial env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, closeChoice⟩) =
      (.ok (), retired env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩ 4) ∧
    lookup ⟨1⟩ (retired env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩ 4) = none ∧
    crashImage ⟨1⟩ ⟨#[0]⟩ (retired env ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩ 4) =
      some ⟨⟨#[1]⟩, 4⟩ := by
  refine ⟨complete_cycle _ _ env registered (by unfold Valid; decide)
    (by simp [blocked, closeChoice])
    (by
      simp [closeStep, action, closeChoice, persist, ← ByteArray.size_data]
      decide), ?_, ?_⟩
  · simp [lookup, retired, closedCell, typeName, closedTypeName, handleTypeName, writableHandleTypeName, closedHandleTypeName]
  · simp [crashImage, lookup, lookupClosed, retired, closedCell, typeName, closedTypeName, handleTypeName, writableHandleTypeName, closedHandleTypeName,
      decode, encode, limit, persist, ← ByteArray.size_data]
    decide

end FileResource.Properties
