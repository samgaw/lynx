module
public import Record.RepairImageInvariant
public import Record.RepeatedRepairProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairImageCrash
open NativeFile Record.CrashProperties Record.LogProperties Record.Properties Record.RecoveryProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.RepeatedRepairProperties Record.RepairImageInvariant

/-- Crashes during any prefix of actual Rust repair retain the acknowledged prefix.
A successful fresh invocation of actual Rust repair recovers every original
record and synchronizes tail removal. Progress requires the declared host script. -/
theorem recover_after_repair_crash (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maxRecords : Usize)
    (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (more : values.length < maxRecords.val) (elapsed : PID → Nat → Nat)
    (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (executed : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_log file maxRecords) elapsed) events last)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage file mask (snapshot env.currentPid last) = some image) :
    repair_log ⟨image.highWater + 1⟩ maxRecords (restarted image (repairScript image.bytes rest)) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨disk (logBytes values), disk (logBytes values), image.bytes.size, rest⟩ []) := by
  have kept := repair_prefix_invariant env file frame values before maxRecords separate valid
    stable visible elapsed events last executed
  obtain ⟨state, equal, admitted, v, d⟩ := kept
  rw [equal] at captured
  unfold crashImage at captured
  rw [lookup_admitted env file state frame separate admitted] at captured
  change (persist state.durable state.visible mask).bind
    (fun bytes => some (⟨bytes, (fileEnv env file state frame).nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj equal
  have sizes := persist_lengths _ _ _ _ persisted
  have protectedImage := persist_log_image _ _ _ _ _ d v persisted
  have bounded : bytes.size ≤ limit := by
    have := admitted.1
    have := admitted.2.1
    omega
  simpa only [repairScript] using restart_repair values
    (⟨bytes, (fileEnv env file state frame).nativeRefCounter⟩ : Image) rest maxRecords protectedImage bounded more

end Record.RepairImageCrash
