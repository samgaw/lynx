module
public import Lynx
public import LockedAwait.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace LockedAwait.Properties
abbrev Bytes := Array U8 2#usize
abbrev Reply := core.result.Result Usize U8
@[expose] def recover :
    core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)) →
      NativeGuard NativeFile
  | .Ok guard => guard
  | .Err error => error.value
@[expose] def initial (mutex : NativeMutex NativeFile) (data : Bytes) : locked_suspended_write.closure :=
  ⟨mutex, data, 0#u32, none, none, none, none, none⟩
@[expose] def pending (mutex : NativeMutex NativeFile) (data : Bytes)
    (guard : NativeGuard NativeFile) (reply : Reply) : locked_suspended_write.closure :=
  ⟨mutex, data, 3#u32, some data, some guard, some reply, some ⟨false⟩, some true⟩
@[expose] def completed (mutex : NativeMutex NativeFile) (data : Bytes) (reply : Reply) :
    locked_suspended_write.closure :=
  ⟨mutex, data, 1#u32, some data, none, some reply, some ⟨false⟩, some false⟩

theorem constructor (mutex : NativeMutex NativeFile) (data : Bytes) :
    locked_suspended_write mutex data = NativeM.ok (initial mutex data) := rfl

theorem unstarted_cleanup (mutex : NativeMutex NativeFile) (data : Bytes) :
    locked_suspended_write.closure.drop_owned (initial mutex data) = NativeM.ok () := by
  simp [locked_suspended_write.closure.drop_owned, initial, NativeM.ok, UScalar.ofNatCore]

theorem suspended_cleanup (mutex : NativeMutex NativeFile) (data : Bytes)
    (guard : NativeGuard NativeFile) (reply : Reply) :
    locked_suspended_write.closure.drop_owned (pending mutex data guard reply) =
      NativeGuard.release guard := by
  simp [locked_suspended_write.closure.drop_owned, pending, NativeOwnedDrop.drop, UScalar.ofNatCore]

theorem completed_cleanup (mutex : NativeMutex NativeFile) (data : Bytes) (reply : Reply) :
    locked_suspended_write.closure.drop_owned (completed mutex data reply) = NativeM.ok () := by
  simp [locked_suspended_write.closure.drop_owned, completed, NativeM.ok, UScalar.ofNatCore]

theorem yield_pending (context : NativeTaskContext) :
    io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll ⟨⟨true⟩⟩ context = (do
      NativeWaker.wakeByRef (NativeTaskContext.waker context)
      NativeM.ok (.Pending, ⟨⟨false⟩⟩, context)) := by
  simp [io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok]

theorem yield_ready (context : NativeTaskContext) :
    io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll ⟨⟨false⟩⟩ context =
      NativeM.ok (.Ready (), ⟨⟨false⟩⟩, context) := by
  simp [io_core.YieldOnce.Insts.CoreFutureFutureFutureTuple.poll,
    core.pin.PinMutAT.get_mut, NativeM.ok]

theorem resume_contract (mutex : NativeMutex NativeFile) (data : Bytes)
    (guard : NativeGuard NativeFile) (reply : Reply) (context : NativeTaskContext) :
    locked_suspended_write.closure.poll ⟨pending mutex data guard reply⟩ context = (do
      NativeGuard.release guard
      NativeM.ok (.Ready reply, ⟨completed mutex data reply⟩, context)) := by
  simp [locked_suspended_write.closure.poll, pending, completed, yield_ready,
    NativeOwnedDrop.drop, NativeM.ok, UScalar.ofNatCore]

theorem first_pending_contract (mutex : NativeMutex NativeFile) (data : Bytes)
    (context : NativeTaskContext) :
    locked_suspended_write.closure.poll ⟨initial mutex data⟩ context = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recover acquired
      let (reply, file) ← io_core.write_once guard.value (Array.to_slice data)
      let result : Reply ← match reply with
        | .Ok count => NativeM.ok (.Ok count)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 1#u8)
      NativeWaker.wakeByRef (NativeTaskContext.waker context)
      NativeM.ok (.Pending, ⟨pending mutex data {guard with value := file} result⟩, context)) := by
  simp [locked_suspended_write.closure.poll, initial, UScalar.ofNatCore, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [recover, NativePoisonError.into_inner, NativeM.lift,
    NativeGuard.deref_mut]
  all_goals
    congr 1
    funext returned
    rcases returned with ⟨reply, file⟩
    cases reply <;> simp [io_core.yield_once,
      core.future.into_future.IntoFuture.Blanket.into_future,
      yield_pending, NativeOwnedDrop.drop, NativeM.ok, pending, bind_assoc, UScalar.ofNatCore]

theorem caller_contract (mutex : NativeMutex NativeFile) (data : Bytes) (resume : Bool) :
    poll_locked_write mutex data resume = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recover acquired
      let (reply, file) ← io_core.write_once guard.value (Array.to_slice data)
      let result : Reply ← match reply with
        | .Ok count => NativeM.ok (.Ok count)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 1#u8)
      NativeGuard.release {guard with value := file}
      NativeM.ok (if resume then some result else none)) := by
  simp [poll_locked_write, constructor, first_pending_contract,
    NativeTaskContext.fromWaker, NativeWaker.noop, NativeWaker.wakeByRef, NativeM.ok, bind_assoc]
  congr 1
  funext acquired
  congr 1
  funext returned
  rcases returned with ⟨reply, file⟩
  cases reply <;> cases resume <;>
    simp [resume_contract, suspended_cleanup, completed_cleanup, NativeM.ok, bind_assoc]

theorem no_panic (mutex : NativeMutex NativeFile) (data : Bytes) (resume : Bool) :
    NativeM.NoPanic (poll_locked_write mutex data resume) := by
  rw [caller_contract]
  apply (NativeM.NoPanic.mutex_lock mutex).bind
  intro acquired
  simp only [io_core.write_once, monadLift_self]
  apply (NativeM.NoPanic.file_write _ _).bind
  rintro ⟨reply, file⟩
  cases reply with
  | Ok count =>
    simp only [NativeM.ok, Result.ok_bind]
    exact (NativeM.NoPanic.guard_release _).bind _ (fun _ => .ok _)
  | Err error =>
    simp only [NativeM.ok]
    apply (NativeM.NoPanic.io_error_dispose error).bind
    intro _
    simp only [Result.ok_bind]
    exact (NativeM.NoPanic.guard_release _).bind _ (fun _ => .ok _)

/-- A ready short or complete write retains its actual count and updated file.
The premises are executable primitive transitions, not assumed Rust contracts. -/
theorem caller_success_prefix (mutex : NativeMutex NativeFile) (data : Bytes) (resume : Bool)
    (acquired : core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile)))
    (count : Usize) (file : NativeFile) (before locked written released : Environment)
    (lock : NativeMutex.pollLock mutex before = some (.ok acquired, locked))
    (write : NativeFile.pollWrite (recover acquired).value (Array.to_slice data) locked =
      some (.ok (.Ok count, file), written))
    (release : NativeGuard.pollRelease {recover acquired with value := file} written =
      some (.ok (), released)) :
    Result.ReadyPrefix (poll_locked_write mutex data resume) before
      (.ok (if resume then some (.Ok count) else none)) released := by
  rw [caller_contract]
  simp only [NativeMutex.lock, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok acquired) _ _ _ _ lock
  simp only [Result.ok_bind, io_core.write_once, monadLift_self,
    NativeFile.write, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok (.Ok count, file)) _ _ _ _ write
  simp only [Result.ok_bind, NativeM.ok, NativeGuard.release, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok ()) _ _ _ _ release
  exact .refl _ _

/-- Write failures consume their admitted OS error before releasing the guard.
Cancellation suppresses the stored reply, not the completed native effects. -/
theorem caller_error_prefix (mutex : NativeMutex NativeFile) (data : Bytes) (resume : Bool)
    (acquired : core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile)))
    (error : NativeIoError) (file : NativeFile)
    (before locked written cleaned released : Environment)
    (lock : NativeMutex.pollLock mutex before = some (.ok acquired, locked))
    (write : NativeFile.pollWrite (recover acquired).value (Array.to_slice data) locked =
      some (.ok (.Err error, file), written))
    (dispose : Result.ReadyPrefix (NativeIoError.dispose error) written (.ok ()) cleaned)
    (release : NativeGuard.pollRelease {recover acquired with value := file} cleaned =
      some (.ok (), released)) :
    Result.ReadyPrefix (poll_locked_write mutex data resume) before
      (.ok (if resume then some (.Err 1#u8) else none)) released := by
  rw [caller_contract]
  simp only [NativeMutex.lock, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok acquired) _ _ _ _ lock
  simp only [Result.ok_bind, io_core.write_once, monadLift_self,
    NativeFile.write, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok (.Err error, file)) _ _ _ _ write
  simp only [Result.ok_bind, NativeM.ok]
  apply (dispose.bind _).trans
  simp only [Result.ok_bind, NativeGuard.release, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok ()) _ _ _ _ release
  exact .refl _ _

end LockedAwait.Properties
