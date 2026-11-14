module
public import Record.RepairAcknowledgement
public import Record.LockedProperties
public import Record.RollbackProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairWriterProperties
open Record.LockedProperties

/-- The actual Rust caller checks repair's result before calling the actual
append/rollback implementation. A recovery limit is not an append acknowledgement. -/
@[cbv_eval] theorem repair_append_contract (file : NativeFile) (maximum : Usize) (value : U16) :
    repair_and_append file maximum value = (do
      let (reply, file) ← repair_log file maximum
      match reply with
      | .Err error => NativeM.ok (.Err error, file)
      | .Ok none => NativeM.ok (.Ok false, file)
      | .Ok (some _) => append_record_or_rollback file value) := by
  simp only [repair_and_append, monadLift_self, NativeM.lift, NativeM.ok, Result.ok_bind]
  apply congrArg (fun next => repair_log file maximum >>= next)
  funext output
  obtain ⟨reply, file⟩ := output
  cases reply with
  | Err error =>
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, core.convert.FromSame.from,
        NativeM.monadLift_eq, NativeM.fromRust_ok]
  | Ok option => cases option <;> rfl

/-- One actual guard covers both repair and append, including all result/error
branches and the compiler-generated release of the returned file identity. -/
@[cbv_eval] theorem critical_contract (mutex : NativeMutex NativeFile) (maximum : Usize) (value : U16) :
    locked_repair_and_append mutex maximum value = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recoverGuard acquired
      let (reply, file) ← repair_and_append guard.value maximum value
      NativeGuard.release {guard with value := file}
      NativeM.ok reply) := by
  simp only [locked_repair_and_append, monadLift_self, NativeM.lift, NativeM.ok, Result.ok_bind,
    NativeGuard.deref_mut, NativeDrop.drop]
  apply congrArg (fun next => NativeMutex.lock mutex >>= next)
  funext acquired
  cases acquired <;> simp [recoverGuard]

end Record.RepairWriterProperties
