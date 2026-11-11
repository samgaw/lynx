module
public import Returned.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Returned.Properties
set_option maxHeartbeats 1000000

/-- The extracted callee implements the full protocol, including its blocking
fallback, rather than an assumed direct acquisition. -/
theorem protocol (mutex : NativeMutex Bool) :
    ownership_base.acquire_or_wait mutex = (do
      let result ← NativeMutex.try_lock mutex
      match result with
      | .Ok guard => NativeM.ok (.Ok guard)
      | .Err (.Poisoned error) => NativeM.ok (.Err error)
      | .Err .WouldBlock => NativeMutex.lock mutex) := by
  unfold ownership_base.acquire_or_wait
  congr 1
  funext result
  cases result with
  | Ok guard => rfl
  | Err error => cases error <;> rfl

theorem toggle (value : Bool) : ownership_base.toggle value = NativeM.ok (!value) := by
  cases value <;> rfl

/-- Both acquired alternatives return ownership of the actual guard. -/
theorem available (value poisoned : Bool) (schedule : List ScheduleChoice) :
    let env : Environment := {
      nativeRefCounter := 1,
      nativeHeap := [(1, NativeMutex.typeName Bool, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])]}
    let guard : NativeGuard Bool := ⟨⟨1⟩, 2, [], value⟩
    (ownership_base.acquire_or_wait ⟨1⟩).run env schedule =
      (.ok (if poisoned then .Err ⟨guard⟩ else .Ok guard),
        {env with
          nativeRefCounter := 2,
          nativeHeap := [(1, NativeMutex.typeName Bool,
            NativeMutex.lockedContents [] 2 poisoned value)]}) := by
  cases value <;> cases poisoned <;>
    simp [protocol, NativeMutex.try_lock, NativeMutex.tryAcquire, NativeMutex.pollLock,
      NativeMutex.typeName, NativeCodec.encode, NativeCodec.decode,
      NativeMutex.lockedContents, NativeM.ok, Result.nativeModify_bind, Result.ofExcept]

/-- A foreign held lease blocks the fallback. Pending work is not a successful
return or a Rust error, under any supplied logical schedule. -/
theorem blocked (value poisoned : Bool) (owner caller : PID) (different : owner ≠ caller)
    (schedule : List ScheduleChoice) :
    let env : Environment := {
      currentPid := caller, nativeRefCounter := 2,
      nativeHeap := [(1, NativeMutex.typeName Bool,
        NativeMutex.lockedContents owner 2 poisoned value)]}
    (ownership_base.acquire_or_wait ⟨1⟩).run env schedule = (.deadlock, env) := by
  cases value <;> cases poisoned <;>
    simp [protocol, NativeMutex.try_lock, NativeMutex.tryAcquire, NativeMutex.lock,
      NativeMutex.pollLock, NativeMutex.typeName, NativeMutex.lockedContents,
      NativeCodec.encode, NativeCodec.decode, NativeM.ok, Result.nativeModify_bind,
      Result.ofExcept, Result.wait_run, different]

/-- The caller consumes the returned guard, commits its mutation on release,
reacquires the shared contents and retires every local native identity. -/
theorem commits (value : Bool) (schedule : List ScheduleChoice) :
    (ownership_app.returned_guard_flip value).run {} schedule =
      (.ok (!value), {nativeRefCounter := 3}) := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [ownership_app.returned_guard_flip,
      protocol, toggle, NativeMutex.new, NativeMutex.lock, NativeMutex.try_lock,
      NativeMutex.tryAcquire, NativeMutex.pollLock, NativeMutex.typeName,
      NativeCodec.decode, NativeCodec.encode, NativeDrop.drop, NativeMutex.dispose,
      NativeM.allocate, NativeM.removeCell, NativeM.readCell, NativeGuard.release,
      NativeGuard.pollRelease, NativeGuard.deref, NativeGuard.deref_mut,
      NativePoisonError.into_inner, NativeM.ok, NativeM.lift, Result.wait_run,
      Result.ofExcept, Result.nativeModify_bind, Result.nativeGet_bind]

end Returned.Properties
