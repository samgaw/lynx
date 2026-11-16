module
public import Lynx
public import GuardedSync.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace GuardedSync.Properties
abbrev Bytes := Array U8 2#usize
abbrev Reply := core.result.Result Usize U8
@[expose] def recover :
    core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)) →
      NativeGuard NativeFile
  | .Ok guard => guard
  | .Err error => error.value
@[expose] def initial (mutex : NativeMutex NativeFile) (data : Bytes) : locked_suspended_sync.closure :=
  ⟨mutex, data, 0#u32, none, none, none, none, none⟩
@[expose] def pending (mutex : NativeMutex NativeFile) (data : Bytes)
    (guard : NativeGuard NativeFile) (reply : Reply) : locked_suspended_sync.closure :=
  ⟨mutex, data, 3#u32, some data, some guard, some reply, some ⟨false⟩, some true⟩
@[expose] def completed (mutex : NativeMutex NativeFile) (data : Bytes) (reply : Reply) :
    locked_suspended_sync.closure :=
  ⟨mutex, data, 1#u32, some data, none, some reply, some ⟨false⟩, some false⟩

theorem constructor (mutex : NativeMutex NativeFile) (data : Bytes) :
    locked_suspended_sync mutex data = NativeM.ok (initial mutex data) := rfl

theorem unstarted_cleanup (mutex : NativeMutex NativeFile) (data : Bytes) :
    locked_suspended_sync.closure.drop_owned (initial mutex data) = NativeM.ok () := by
  simp [locked_suspended_sync.closure.drop_owned, initial, NativeM.ok, UScalar.ofNatCore]

theorem suspended_cleanup (mutex : NativeMutex NativeFile) (data : Bytes)
    (guard : NativeGuard NativeFile) (reply : Reply) :
    locked_suspended_sync.closure.drop_owned (pending mutex data guard reply) =
      NativeGuard.release guard := by
  simp [locked_suspended_sync.closure.drop_owned, pending, NativeOwnedDrop.drop, UScalar.ofNatCore]

theorem completed_cleanup (mutex : NativeMutex NativeFile) (data : Bytes) (reply : Reply) :
    locked_suspended_sync.closure.drop_owned (completed mutex data reply) = NativeM.ok () := by
  simp [locked_suspended_sync.closure.drop_owned, completed, NativeM.ok, UScalar.ofNatCore]

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

/-- The separate first-party helper preserves write errors and synchronizes only
successful writes. Its count acknowledges the actual written prefix. -/
theorem synchronize_contract (file : NativeFile) (written : Reply) :
    synchronize_written file written = (match written with
      | .Ok count => do
        let result ← NativeFile.syncAll file
        match result with
        | .Ok () => NativeM.ok (.Ok count)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 2#u8)
      | .Err error => NativeM.ok (.Err error)) := by
  cases written <;> simp [synchronize_written, io_core.synchronize,
    NativeOwnedDrop.drop, NativeM.ok]
  congr 1

theorem resume_contract (mutex : NativeMutex NativeFile) (data : Bytes)
    (guard : NativeGuard NativeFile) (written : Reply) (context : NativeTaskContext) :
    locked_suspended_sync.closure.poll ⟨pending mutex data guard written⟩ context = (do
      let result ← synchronize_written guard.value written
      NativeGuard.release guard
      NativeM.ok (.Ready result, ⟨completed mutex data written⟩, context)) := by
  simp [locked_suspended_sync.closure.poll, pending, completed, yield_ready,
    NativeGuard.deref, NativeOwnedDrop.drop, NativeM.ok, UScalar.ofNatCore]

theorem first_pending_contract (mutex : NativeMutex NativeFile) (data : Bytes)
    (context : NativeTaskContext) :
    locked_suspended_sync.closure.poll ⟨initial mutex data⟩ context = (do
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
  simp [locked_suspended_sync.closure.poll, initial, UScalar.ofNatCore, NativeM.ok]
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
    poll_locked_sync mutex data resume = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recover acquired
      let (reply, file) ← io_core.write_once guard.value (Array.to_slice data)
      let written : Reply ← match reply with
        | .Ok count => NativeM.ok (.Ok count)
        | .Err error => do
          NativeIoError.dispose error
          NativeM.ok (.Err 1#u8)
      let result ← if resume then do
        let synced ← synchronize_written file written
        NativeM.ok (some synced)
      else NativeM.ok none
      NativeGuard.release {guard with value := file}
      NativeM.ok result) := by
  simp [poll_locked_sync, constructor, first_pending_contract,
    NativeTaskContext.fromWaker, NativeWaker.noop, NativeWaker.wakeByRef, NativeM.ok, bind_assoc]
  congr 1
  funext acquired
  congr 1
  funext returned
  rcases returned with ⟨reply, file⟩
  cases reply <;> cases resume <;>
    simp [resume_contract, suspended_cleanup, completed_cleanup, NativeM.ok, bind_assoc]

theorem synchronize_no_panic (file : NativeFile) (written : Reply) :
    NativeM.NoPanic (synchronize_written file written) := by
  rw [synchronize_contract]
  cases written with
  | Err code => exact .ok _
  | Ok count =>
    apply (NativeM.NoPanic.file_sync file).bind
    intro result
    cases result with
    | Ok value => cases value; exact .ok _
    | Err error => exact (NativeM.NoPanic.io_error_dispose error).bind _ (fun _ => .ok _)

private theorem finish_no_panic (guard : NativeGuard NativeFile) (written : Reply) (resume : Bool) :
    NativeM.NoPanic (do
      let result ← if resume then do
        let synced ← synchronize_written guard.value written
        NativeM.ok (some synced)
      else NativeM.ok none
      NativeGuard.release guard
      NativeM.ok result) := by
  cases resume with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, NativeM.ok, Result.ok_bind]
    exact (NativeM.NoPanic.guard_release guard).bind _ (fun _ => .ok _)
  | true =>
    simp only [↓reduceIte, NativeM.ok, Result.ok_bind]
    exact (synchronize_no_panic guard.value written).bind _
      (fun _ => (NativeM.NoPanic.guard_release guard).bind _ (fun _ => .ok _))

theorem no_panic (mutex : NativeMutex NativeFile) (data : Bytes) (resume : Bool) :
    NativeM.NoPanic (poll_locked_sync mutex data resume) := by
  rw [caller_contract]
  apply (NativeM.NoPanic.mutex_lock mutex).bind
  intro acquired
  simp only [io_core.write_once, monadLift_self]
  apply (NativeM.NoPanic.file_write _ _).bind
  rintro ⟨reply, file⟩
  cases reply with
  | Ok count =>
    simpa only [NativeM.ok, Result.ok_bind] using
      finish_no_panic {recover acquired with value := file} (.Ok count) resume
  | Err error =>
    apply (NativeM.NoPanic.io_error_dispose error).bind
    intro _
    simpa only [NativeM.ok, Result.ok_bind] using
      finish_no_panic {recover acquired with value := file} (.Err 1#u8) resume

end GuardedSync.Properties
