module
public import Record.RepairPrefixInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairAppendPrefixInvariant
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.RecoveryProperties Record.ResizeProperties Record.RepairCrashProperties
  Record.AppendPrefixInvariant

/-- Actual repair and append preserve every old acknowledgement at every ready
prefix, including failures and incomplete operations. No new success is assumed. -/
theorem repair_append_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State)
    (maximum : Usize) (value : U16) (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (PrefixInvariant env file frame (disk (logBytes values)))
      (repair_and_append file maximum value) (fileEnv env file before frame) := by
  rw [Record.RepairWriterProperties.repair_append_contract]
  have prefixSafe := Record.RepairPrefixInvariant.repair_log_invariant env file frame values before maximum
    separate valid stable image
  apply Result.NativeInvariant.bind (computation := repair_log file maximum) prefixSafe
  intro output world trace
  have kept := (prefixSafe _ _ trace).1
  obtain ⟨reply,repairedFile⟩ := output
  cases reply with
  | Err error => exact .ok _ _ _ kept
  | Ok option =>
      cases option with
      | none => exact .ok _ _ _ kept
      | some records =>
          obtain ⟨tail,contents⟩ := Record.EncodedPrefixRecovery.prefix_shape values before.visible image
          obtain ⟨identity,_,_⟩ := Record.RepairPrefixReturn.repair_returns_prefix file env frame before values tail maximum
            records repairedFile world separate valid stable contents trace
          subst repairedFile
          obtain ⟨state,rfl,admitted,v,d⟩ := kept
          exact append_invariant env file frame _ state value separate admitted v d

/-- Every raw execution prefix retains old acknowledged records, including a
blocked wait, returned I/O error, unsuccessful rollback or verification cutoff. -/
theorem repair_append_prefix_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State)
    (maximum : Usize) (value : U16) (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_and_append file maximum value) elapsed) events last) :
    PrefixInvariant env file frame (disk (logBytes values))
      (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) := by
  exact prefix_run env file frame _ before _
    (repair_append_invariant env file frame values before maximum value separate valid stable image)
    elapsed events last run

/-- Crashes anywhere in actual repair/append permit actual capped recovery of
all old acknowledgements under the declared successful fresh read script.
No success, terminal result, repaired suffix or exact new log is assumed. -/
theorem recover_after_repair_append_prefix (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State)
    (maximum : Usize) (value : U16) (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_and_append file maximum value) elapsed) events last)
    (mask : ByteArray) (crash : Image) (rest : Term)
    (captured : crashImage file mask (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) = some crash) :
    ∃ (capacity : values.length ≤ 262144),
      recover_log ⟨crash.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (restarted crash (recoveryScript crash.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨crash.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨crash.highWater + 1⟩
            (scanning crash.bytes rest (4 * values.length)) []) := by
  exact recover_prefix_image env file frame values _ separate
    (repair_append_prefix_invariant env file frame values before maximum value separate valid stable image
      elapsed events last run) mask crash rest captured

end Record.RepairAppendPrefixInvariant
