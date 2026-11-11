module
public import TryRw.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace TryRw.Properties
set_option maxHeartbeats 1000000

theorem toggle (value : Bool) : ownership_base.toggle value = NativeM.ok (!value) := by
  cases value <;> rfl

/-- Either lock mode conflicts with an existing writer, including the caller.
Poison does not turn contention into an acquired guard. -/
theorem held (value poisoned : Bool) (owner caller : PID) (schedule : List ScheduleChoice) :
    let env : Environment := {
      currentPid := caller, nativeRefCounter := 2,
      nativeHeap := [(1, NativeRwLock.typeName Bool,
        NativeRwLock.contents (α := Bool) ⟨[], some (2, owner), poisoned, value⟩)]}
    (ownership_base.try_rw_toggle ⟨1⟩).run env schedule = (.ok false, env) ∧
    (ownership_base.try_rw_read ⟨1⟩).run env schedule = (.ok (false, false), env) := by
  cases value <;> cases poisoned <;> simp (config := {maxSteps := 500000}) [ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]

/-- A shared reader prevents mutation; a second reader can still observe the
same cell, and releasing it preserves the original reader's capability. -/
theorem shared (value poisoned : Bool) (owner caller : PID) (schedule : List ScheduleChoice) :
    let env : Environment := {
      currentPid := caller, nativeRefCounter := 2,
      nativeHeap := [(1, NativeRwLock.typeName Bool,
        NativeRwLock.contents (α := Bool) ⟨[(2, owner)], none, poisoned, value⟩)]}
    (ownership_base.try_rw_toggle ⟨1⟩).run env schedule = (.ok false, env) ∧
    (ownership_base.try_rw_read ⟨1⟩).run env schedule =
      (.ok (true, value), {env with nativeRefCounter := 3}) := by
  cases value <;> cases poisoned <;> simp (config := {maxSteps := 500000}) [ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]

/-- Successful and poisoned exclusive acquisition both commit the actual
first-party mutation and release the lease. -/
theorem available (value poisoned : Bool) (schedule : List ScheduleChoice) :
    let env : Environment := {
      nativeRefCounter := 1,
      nativeHeap := [(1, NativeRwLock.typeName Bool,
        NativeRwLock.contents (α := Bool) ⟨[], none, poisoned, value⟩)]}
    (ownership_base.try_rw_toggle ⟨1⟩).run env schedule =
      (.ok true, {env with
        nativeRefCounter := 2,
        nativeHeap := [(1, NativeRwLock.typeName Bool,
          NativeRwLock.contents (α := Bool) ⟨[], none, poisoned, !value⟩)]}) := by
  cases value <;> cases poisoned <;> simp (config := {maxSteps := 500000}) [ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]

/-- Actual cross-crate rejection, update and read-back retire the local cell. -/
theorem cycle (value : Bool) (schedule : List ScheduleChoice) :
    (ownership_app.try_rw_cycle value).run {} schedule =
      (.ok (false, false, true, !value), {nativeRefCounter := 5}) := by
  cases value <;> simp (config := {maxSteps := 500000}) [ownership_app.try_rw_cycle, ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]
/-- Pending writers do not silently select an operating-system priority. -/
theorem queued (value : Bool) (owner : PID) (schedule : List ScheduleChoice) :
    let lock : NativeRwLock Bool := ⟨1⟩
    let env : Environment := {
      nativeRefCounter := 2,
      nativeHeap := [(2, NativeRwLock.writerRequestType lock,
        .tuple #[.nativeReference 1, .pid owner]),
        (1, NativeRwLock.typeName Bool,
          NativeRwLock.contents (α := Bool) ⟨[], none, false, value⟩)]}
    (ownership_base.try_rw_toggle lock).run env schedule = (.error .exhausted, env) ∧
    (ownership_base.try_rw_read lock).run env schedule = (.error .exhausted, env) := by
  cases value <;> simp (config := {maxSteps := 500000}) [ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]

/-- An absent native cell cannot be decoded into a successful lock attempt. -/
theorem invalid (schedule : List ScheduleChoice) :
    (ownership_base.try_rw_toggle ⟨1⟩).run {} schedule = (.error .exhausted, {}) ∧
    (ownership_base.try_rw_read ⟨1⟩).run {} schedule = (.error .exhausted, {}) := by
  simp [ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]
end TryRw.Properties
