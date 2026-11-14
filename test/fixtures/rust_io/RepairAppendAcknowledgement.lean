module
public import Record.AppendAcknowledgement
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairAppendAcknowledgement
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.RecoveryProperties Record.ResizeProperties Record.IntegrityProperties Record.AppendProperties Record.RepairCrashProperties
  Record.RecoveryScanInvariant Record.AppendAcknowledgement

private theorem encoded_append (values : List U16) (value : U16) :
    overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload value)) 4 =
      disk (logBytes (values ++ [value])) := by
  apply ByteArray.ext
  apply _root_.Array.toList_inj.mp
  simpa [logBytes, disk, encoded, fourBytes, layout, rawByte] using
    append_bytes (disk (logBytes values)) value

/-- Under arbitrary admitted host outcomes, a true return from the actual
repair/append caller acknowledges all old records followed by exactly its value.
The successful prefix is evidence, not an assumed first-party contract. -/
theorem repair_append_returns (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (maximum : Usize)
    (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : LogImage values before.visible)
    (trace : Result.ReadyPrefix (repair_and_append file maximum value) (fileEnv env file before frame)
      (.ok (.Ok true, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = disk (logBytes (values ++ [value])) ∧
      after.durable = disk (logBytes (values ++ [value])) ∧ Admitted after := by
  rw [Record.RepairWriterProperties.repair_append_contract] at trace
  obtain ⟨⟨reply, repairedFile⟩, middle, repairedTrace, continuation⟩ := trace.bind_returns
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok option =>
      cases option with
      | none =>
          simp only [NativeM.ok] at continuation
          cases continuation
      | some records =>
          obtain ⟨identity, recovered, repaired, rfl, visible, durable, admitted⟩ :=
            Record.RepairAcknowledgement.repair_returns file env frame before values maximum records repairedFile middle
              separate valid stable image repairedTrace
          subst repairedFile
          obtain ⟨identity, after, rfl, appended, synced, afterValid⟩ :=
            append_returns file value env frame repaired true returnedFile world separate admitted continuation
          have expected : after.visible = disk (logBytes (values ++ [value])) := by
            simpa only [↓reduceIte, visible, encoded_append] using appended
          exact ⟨identity, after, rfl, expected, synced.trans expected, afterValid⟩

private theorem forget_invariant {holds : Environment → Prop} {computation : Result α} {env : Environment}
    (safe : Result.NativeInvariant holds computation env) :
    Result.NativeInvariant (fun _ => True) computation env := by
  intro residual after trace
  exact ⟨trivial, (safe residual after trace).2⟩

private theorem repair_append_fragment (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (maximum : Usize)
    (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : LogImage values before.visible) :
    Result.NativeInvariant (fun _ => True) (repair_and_append file maximum value)
      (fileEnv env file before frame) := by
  rw [Record.RepairWriterProperties.repair_append_contract]
  have repair := forget_invariant (Record.RepairImageInvariant.repair_log_invariant env file frame values
    before maximum separate valid stable image)
  apply Result.NativeInvariant.bind (computation := repair_log file maximum) repair
  intro output world _
  obtain ⟨reply, file⟩ := output
  cases reply with
  | Err error => exact .ok _ _ _ trivial
  | Ok option =>
      cases option with
      | none => exact .ok _ _ _ trivial
      | some records => exact append_fragment file value world

/-- This is a postcondition for every successful terminal raw runtime execution
of actual Rust repair and append. Blocking and failure cannot supply success. -/
theorem repair_append_run_acknowledges (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (maximum : Usize)
    (returnedFile : NativeFile) (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_and_append file maximum value) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok true, returnedFile))) :
    returnedFile = file ∧ ∃ after,
      last = .start (fileEnv env file after frame) (.ok (.Ok true, returnedFile)) elapsed ∧
      after.visible = disk (logBytes (values ++ [value])) ∧
      after.durable = disk (logBytes (values ++ [value])) ∧ Admitted after := by
  have localTrace := repair_append_fragment file value env frame before values maximum separate valid stable image
  obtain ⟨world, trace, ending⟩ := localTrace.run_returns elapsed run terminal
  obtain ⟨identity, after, rfl, visible, durable, admitted⟩ :=
    repair_append_returns file value env frame before values maximum returnedFile world separate valid stable image trace
  exact ⟨identity, after, ending, visible, durable, admitted⟩

/-- Each successful call consumes the previous call's actual resulting file
state. The two scripts and bounds need not agree or be selected in advance. -/
theorem repair_append_twice (file : NativeFile) (first second : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (firstMaximum secondMaximum : Usize) (middleFile returnedFile : NativeFile)
    (middle world : Environment) (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : LogImage values before.visible)
    (firstTrace : Result.ReadyPrefix (repair_and_append file firstMaximum first)
      (fileEnv env file before frame) (.ok (.Ok true, middleFile)) middle)
    (secondTrace : Result.ReadyPrefix (repair_and_append middleFile secondMaximum second)
      middle (.ok (.Ok true, returnedFile)) world) :
    middleFile = file ∧ returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = disk (logBytes (values ++ [first,second])) ∧
      after.durable = disk (logBytes (values ++ [first,second])) ∧ Admitted after := by
  obtain ⟨identity, afterFirst, rfl, firstVisible, firstDurable, firstValid⟩ :=
    repair_append_returns file first env frame before values firstMaximum middleFile middle
      separate valid stable image firstTrace
  subst middleFile
  have firstStable : afterFirst.durable = afterFirst.visible := firstDurable.trans firstVisible.symm
  have firstImage : LogImage (values ++ [first]) afterFirst.visible := by
    rw [firstVisible]
    simpa only [List.append_nil] using log_image (values ++ [first]) [] (by decide)
  obtain ⟨identity, after, rfl, visible, durable, admitted⟩ :=
    repair_append_returns file second env frame afterFirst (values ++ [first]) secondMaximum returnedFile world
      separate firstValid firstStable firstImage secondTrace
  exact ⟨rfl, identity, after, rfl, by simpa [List.append_assoc] using visible,
    by simpa [List.append_assoc] using durable, admitted⟩

@[expose] def snapshot (pid : PID) : Concurrent.Config α → Environment
  | .start env .. => env
  | .running state .. => state.nativeView pid

/-- Every admitted crash after a true raw-runtime acknowledgement retains the
old records plus the new record exactly. Actual fresh repair recovers them under
its declared successful retry script and a sufficient independent retry limit. -/
theorem acknowledged_crash_retry (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (maximum : Usize)
    (returnedFile : NativeFile) (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (image : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_and_append file maximum value) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok true, returnedFile)))
    (mask : ByteArray) (crash : Image) (rest : Term) (retryLimit : Usize)
    (enough : (values ++ [value]).length < retryLimit.val)
    (captured : crashImage file mask (snapshot env.currentPid last) = some crash) :
    crash.bytes = disk (logBytes (values ++ [value])) ∧
      repair_log ⟨crash.highWater + 1⟩ retryLimit
        (restarted crash (Record.RepeatedRepairProperties.repairScript crash.bytes rest)) =
        (.ok (.Ok (some (alloc.vec.Vec.from (values ++ [value]) (by scalar_tac))), ⟨crash.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨crash.highWater + 1⟩
            ⟨disk (logBytes (values ++ [value])), disk (logBytes (values ++ [value])), crash.bytes.size, rest⟩ []) := by
  obtain ⟨identity, after, ending, visible, durable, admitted⟩ :=
    repair_append_run_acknowledges file value env frame before values maximum returnedFile
      separate valid stable image elapsed events last run terminal
  rw [ending] at captured
  simp only [snapshot] at captured
  unfold crashImage at captured
  rw [lookup_admitted env file after frame separate admitted] at captured
  change (persist after.durable after.visible mask).bind
    (fun bytes => some (⟨bytes, (fileEnv env file after frame).nativeRefCounter⟩ : Image)) = some crash at captured
  obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj equal
  rw [visible, durable] at persisted
  have same := Record.RecoveryProperties.persist_same _ mask bytes persisted
  refine ⟨same, ?_⟩
  apply restart_repair (values ++ [value]) _ rest retryLimit
  · rw [same]
    simpa only [List.append_nil] using log_image (values ++ [value]) [] (by decide)
  · rw [same]
    have bounded := admitted.1
    rw [visible] at bounded
    exact bounded
  · exact enough

end Record.RepairAppendAcknowledgement
