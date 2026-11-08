module
public import Record.RollbackProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.SharedLogProperties
open NativeFile Record.LockedProperties

/-- The compiled export consumes its decoded resource owner on both normal
Rust outcomes and consumes the I/O error before returning false. -/
theorem facade_contract (resource : NativeResourceArc shared_log.LogResource) (value : U16) :
    __APPEND__ resource value = (do
      let reply ← shared_log.append resource value
      NativeOwnedDrop.drop resource
      match reply with
      | .Ok accepted => NativeM.ok accepted
      | .Err error => do
        NativeOwnedDrop.drop error
        NativeM.ok false) := by
  unfold __APPEND__
  rfl

/-- The actual facade borrows the shared allocation, acquires its file mutex,
executes the extracted append/rollback implementation and releases the guard.
The file identity is read from the allocation, never copied from an argument. -/
theorem critical_contract (resource : NativeResourceArc shared_log.LogResource) (value : U16) :
    shared_log.append resource value = (do
      let log ← NativeResourceArc.deref resource
      let acquired ← NativeMutex.lock log.file
      let guard := recoverGuard acquired
      let (reply, file) ← append_record_or_rollback guard.value value
      NativeGuard.release {guard with value := file}
      NativeM.ok reply) := by
  simp only [shared_log.append, monadLift_self, Record.RollbackProperties.critical_contract]

/-- Multiple decoded owners observe the same critical section. The validated
resource read changes neither the owner registry nor the shared file state. -/
theorem borrow_prefix (resource : NativeResourceArc shared_log.LogResource)
    (log : shared_log.LogResource) (value : U16) (count : Nat) (env : Environment)
    (positive : 0 < count) (bounded : count ≤ NativeResourceArc.referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == resource.token) =
      [(resource.token, NativeResourceArc.handleType shared_log.LogResource, .nativeReference resource.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == resource.id) =
      [(resource.id, NativeResourceArc.typeName shared_log.LogResource,
        .tuple #[.integer count, NativeCodec.encode log])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType shared_log.LogResource &&
        cell.2.2 == .nativeReference resource.id).length = count) :
    Result.ReadyPrefix (shared_log.append resource value) env
      (locked_append_or_rollback log.file value) env := by
  have trace := (NativeResourceArc.deref_live_prefix resource log count env positive bounded
    token stored owners).bind (fun log => locked_append_or_rollback log.file value)
  simpa only [shared_log.append, monadLift_self, Result.ok_bind] using trace

@[expose] def logPayload : shared_log.LogResource := {file := ⟨1⟩}

/-- One VM pin and two decoded Rust owners share the same mutex and file.
The file bytes remain in their independent mutable heap cell. -/
@[expose] def overlappingEnv (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 8, nativeHeap := [
    (8, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (7, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (6, NativeResourceArc.termType shared_log.LogResource, .tuple #[.nativeReference 3, .nativeReference 5]),
    (5, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (3, NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 3, NativeCodec.encode logPayload]),
    (1, NativeMutex.typeName NativeFile, Record.LockedConcurrent.free),
    (2, NativeFile.typeName, NativeFile.encode state)]}

/-- Both actual Rust borrowers reach the same lock identity in the same heap.
Each conjunct is a local prefix; this does not assume a concurrent schedule. -/
theorem aliasing_prefix (env : Environment) (state : State) (first second : U16) :
    Result.ReadyPrefix (shared_log.append ⟨3,7⟩ first) (overlappingEnv env state)
      (locked_append_or_rollback ⟨1⟩ first) (overlappingEnv env state) ∧
    Result.ReadyPrefix (shared_log.append ⟨3,8⟩ second) (overlappingEnv env state)
      (locked_append_or_rollback ⟨1⟩ second) (overlappingEnv env state) := by
  constructor
  all_goals
    apply borrow_prefix _ logPayload _ 3 _ (by decide) (by decide)
    all_goals simp [overlappingEnv, logPayload, NativeResourceArc.handleType,
      NativeResourceArc.typeName, NativeResourceArc.termType, NativeCodec.typeName,
      NativeMutex.typeName, NativeFile.typeName, NativeCodec.encode, List.filter]

/-- A complete write returns true after the actual synchronization
and guard-release steps. Poll equations admit arbitrary framed resource cells. -/
theorem full_write (mutex : NativeMutex NativeFile) (value : U16)
    (guard : NativeGuard NativeFile) (acquired : core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile)))
    (s0 s1 s2 s3 s4 s5 : Environment) (position : U64)
    (lock : NativeMutex.pollLock mutex s0 = some (.ok acquired, s1))
    (recovered : recoverGuard acquired = guard)
    (seek : pollSeek guard.value (.end_ 0#i64) s1 = some (.ok (.Ok position, guard.value), s2))
    (write : pollWrite guard.value (Record.CrashProperties.payload value) s2 =
      some (.ok (.Ok 4#usize, guard.value), s3))
    (sync : pollSync guard.value s3 = some (.ok (.Ok ()), s4))
    (release : NativeGuard.pollRelease guard s4 = some (.ok (), s5)) :
    Result.ReadyPrefix (locked_append_or_rollback mutex value) s0 (.ok (.Ok true)) s5 := by
  rw [Record.RollbackProperties.critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _ lock ?_
  simp only [Result.ok_bind, recovered, Record.RollbackProperties.append_contract,
    bind_assoc, NativeFile.seek, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _ seek ?_
  simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _ write ?_
  simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _ sync ?_
  simp only [Result.ok_bind, NativeM.ok, NativeGuard.release, Result.wait_bind]
  exact .wait _ _ _ _ _ _ _ release (.refl _ _)

end Record.SharedLogProperties
