module
public import TryLock.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace TryLock.Properties
set_option maxHeartbeats 1000000

/-- The actual low-level mutation is reused by both acquisition branches. -/
theorem toggle (value : Bool) : ownership_base.toggle value = NativeM.ok (!value) := by
  cases value <;> rfl

/-- A held mutex rejects a nonblocking update without changing any shared state,
including when the caller itself owns the lock or the lock is poisoned. -/
theorem held (value poisoned : Bool) (owner caller : PID) (schedule : List ScheduleChoice) :
    let env : Environment := {
      currentPid := caller, nativeRefCounter := 2,
      nativeHeap := [(1, NativeMutex.typeName Bool,
        NativeMutex.lockedContents owner 2 poisoned value)]}
    (ownership_base.try_toggle ⟨1⟩).run env schedule = (.ok false, env) := by
  cases value <;> cases poisoned <;>
    simp [ownership_base.try_toggle, NativeMutex.try_lock, NativeMutex.tryAcquire,
      NativeMutex.lockedContents, NativeMutex.typeName, NativeCodec.decode,
      NativeCodec.encode, NativeM.ok, Result.ofExcept, Result.nativeModify_bind]

/-- An available poisoned lock still transfers an owned guard and commits the
actual first-party mutation when that guard is released. -/
theorem available (value poisoned : Bool) (schedule : List ScheduleChoice) :
    let env : Environment := {
      nativeRefCounter := 1,
      nativeHeap := [(1, NativeMutex.typeName Bool, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])]}
    (ownership_base.try_toggle ⟨1⟩).run env schedule =
      (.ok true, {env with
        nativeRefCounter := 2,
        nativeHeap := [(1, NativeMutex.typeName Bool, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode (!value)])]}) := by
  cases value <;> cases poisoned <;>
    simp [ownership_base.try_toggle, toggle, NativeMutex.try_lock, NativeMutex.tryAcquire,
      NativeMutex.pollLock, NativeMutex.typeName, NativeCodec.decode, NativeCodec.encode,
      NativeDrop.drop, NativeGuard.release, NativeGuard.pollRelease,
      NativeGuard.deref_mut, NativePoisonError.into_inner, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeGet_bind]

/-- Both actual workspace crates participate in the rejected-then-successful
critical section. A failed attempt allocates no logical acquisition token. -/
theorem cycle (value : Bool) (schedule : List ScheduleChoice) :
    (ownership_app.try_cycle value).run {} schedule =
      (.ok (false, value, true, !value), {nativeRefCounter := 4}) := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [ownership_app.try_cycle,
      ownership_base.try_toggle, toggle, NativeMutex.new, NativeMutex.lock,
      NativeMutex.try_lock, NativeMutex.tryAcquire, NativeMutex.pollLock,
      NativeMutex.typeName, NativeCodec.decode, NativeCodec.encode,
      NativeDrop.drop, NativeMutex.dispose, NativeM.allocate, NativeM.removeCell, NativeM.readCell,
      NativeGuard.release, NativeGuard.pollRelease, NativeGuard.deref,
      NativeGuard.deref_mut, NativePoisonError.into_inner, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeGet_bind]

end TryLock.Properties
