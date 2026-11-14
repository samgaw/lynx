module
public import Record.RepairAcknowledgement
public import Record.LockedProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.LockedRepairProperties
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.ResizeProperties Record.RepairCrashProperties Record.RecoveryScanInvariant
  Record.RepeatedRepairProperties Record.LockedProperties

/-- The extracted Rust wrapper retains the guard through parsing, truncation
and sync, then releases it with the returned file identity on every IO result. -/
@[cbv_eval] theorem critical_contract (mutex : NativeMutex NativeFile) (maximum : Usize) :
    locked_repair mutex maximum = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recoverGuard acquired
      let (reply, file) ← repair_log guard.value maximum
      NativeGuard.release {guard with value := file}
      NativeM.ok reply) := by
  simp only [locked_repair, monadLift_self, NativeM.lift, NativeM.ok, Result.ok_bind,
    NativeGuard.deref_mut, NativeDrop.drop]
  apply congrArg (fun next => NativeMutex.lock mutex >>= next)
  funext acquired
  cases acquired <;> simp [recoverGuard]

/-- Every prefix of the actual repair body retains the held mutex and excludes
an attempted peer acquisition. Inputs and host scripts are arbitrary within
the independent-file image admission, including blocked and error outcomes. -/
theorem body_excludes_peer (env : Environment) (owner peer : PID) (token : Nat)
    (frame : List (Nat × String × Term))
    (apartFile : Separate (⟨2⟩ : NativeFile) frame)
    (apartMutex : ∀ cell ∈ frame, cell.1 ≠ 1)
    (values : List U16) (before : State) (maximum : Usize)
    (different : owner ≠ peer) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (trace : Result.ReadyPrefix (repair_log ⟨2⟩ maximum)
      (fileEnv env ⟨2⟩ before ((1, NativeMutex.typeName NativeFile,
        NativeMutex.lockedContents owner token false (⟨2⟩ : NativeFile)) :: frame)) residual world) :
    NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile) {world with currentPid := peer} = none ∧
      ImageInvariant env ⟨2⟩ ((1, NativeMutex.typeName NativeFile,
        NativeMutex.lockedContents owner token false (⟨2⟩ : NativeFile)) :: frame) values world := by
  have safe := Record.RepairImageInvariant.repair_log_invariant env ⟨2⟩
    ((1, NativeMutex.typeName NativeFile, NativeMutex.lockedContents owner token false (⟨2⟩ : NativeFile)) :: frame)
    values before maximum (by simp [Separate] at apartFile ⊢; exact apartFile) admitted stable visible
  have kept := (safe _ _ trace).1
  refine ⟨?_, kept⟩
  obtain ⟨after, rfl, _⟩ := kept
  have filtered : frame.filter (fun cell => cell.1 == 1) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro cell member
    simpa using apartMutex cell member
  simp [NativeMutex.pollLock, fileEnv, NativeMutex.lockedContents, NativeMutex.typeName,
    NativeCodec.decode, NativeCodec.encode, NativeCodec.typeName, different, filtered]

end Record.LockedRepairProperties
