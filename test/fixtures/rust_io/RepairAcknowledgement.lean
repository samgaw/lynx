module
public import Record.RepairImageInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairAcknowledgement
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.CrashProperties Record.LogProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.RecoveryScanInvariant

private theorem resize_step_returns (before : State) (length : U64) (after : State)
    (valid : Admitted before) (step : setLenStep before length = some (.Ok (), after)) :
    after.visible = resize before.visible length.val ∧ after.position = before.position ∧ Admitted after := by
  unfold setLenStep at step
  split at step
  · contradiction
  · rename_i bounded
    cases chosen : action "set_len" before.script with
    | none => simp [chosen] at step
    | some choice =>
        obtain ⟨success, value, mask, rest⟩ := choice
        simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
        cases success
        · cases accepted : persist before.durable before.visible mask with
          | none => simp [accepted] at step
          | some data => simp [accepted] at step
        · simp only [↓reduceIte] at step
          split at step
          · contradiction
          · cases accepted : persist before.durable (resize before.visible length.val) mask with
            | none => simp [accepted] at step
            | some data =>
                simp only [accepted, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
                obtain ⟨_, rfl⟩ := step
                exact ⟨rfl, rfl, resize_admitted before length mask data rest valid (by omega) accepted⟩

private theorem resize_returns [heapLayout : Record.Properties.HeapLayout] (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result Unit NativeIoError) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (io_core.resize_to file length) (fileEnv env file before frame) (.ok reply) world) :
    ∃ after, world = fileEnv env file after frame ∧ setLenStep before length = some (reply, after) := by
  simp only [io_core.resize_to, NativeFile.setLen, monadLift_self] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollSetLen at ready
          rw [no_shared_handle_at env file before frame separate,
            lookup_admitted env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : setLenStep before length with
            | none => simp [step] at ready
            | some outcome =>
                obtain ⟨reply, after⟩ := outcome
                simp only [step] at ready
                obtain ⟨rfl, rfl⟩ := ready
                exact ⟨after, store_at env file before after frame separate, rfl⟩

private theorem sync_step_returns (before after : State)
    (step : syncStep before = some (.Ok (), after)) :
    after.visible = before.visible ∧ after.durable = before.visible ∧ after.position = before.position := by
  unfold syncStep at step
  cases chosen : action "sync_all" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, value, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases success
      · cases accepted : persist before.durable before.visible mask with
        | none => simp [accepted] at step
        | some data => simp [accepted] at step
      · simp only [↓reduceIte] at step
        split at step
        · contradiction
        · simp only [Option.some.injEq, Prod.mk.injEq] at step
          obtain ⟨_, rfl⟩ := step
          exact ⟨rfl, rfl, rfl⟩

/-- Successful synchronization preserves the visible bytes and cursor and makes
the durable image exactly those bytes, for every admitted host script. -/
theorem synchronize_returns [heapLayout : Record.Properties.HeapLayout] (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (io_core.synchronize file) (fileEnv env file before frame)
      (.ok (.Ok ())) world) :
    ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ after.position = before.position := by
  simp only [io_core.synchronize, NativeFile.syncAll, monadLift_self] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollSync at ready
          rw [lookup_admitted env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : syncStep before with
            | none => simp [step] at ready
            | some outcome =>
                obtain ⟨reply, after⟩ := outcome
                simp only [step] at ready
                obtain ⟨rfl, rfl⟩ := ready
                exact ⟨after, store_at env file before after frame separate, sync_step_returns before after step⟩

/-- A successful actual resize/sync call has made both images exactly the
requested resize, under every admitted host script. A failed or blocked sync
cannot provide the successful-prefix premise. -/
theorem resize_then_sync_returns [heapLayout : Record.Properties.HeapLayout] (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (resize_then_sync file length) (fileEnv env file before frame)
      (.ok (.Ok ())) world) :
    ∃ after, world = fileEnv env file after frame ∧
      after.visible = resize before.visible length.val ∧ after.durable = resize before.visible length.val ∧
      after.position = before.position ∧ Admitted after := by
  simp only [resize_then_sync, monadLift_self] at trace
  obtain ⟨reply, middle, resizedTrace, continuation⟩ := trace.bind_returns
  obtain ⟨resizedState, rfl, step⟩ := resize_returns file length env frame before reply middle separate valid resizedTrace
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok returnedUnit =>
      cases returnedUnit
      obtain ⟨visible, position, admitted⟩ := resize_step_returns before length resizedState valid step
      obtain ⟨after, rfl, v, d, p⟩ := synchronize_returns file env frame resizedState world separate admitted continuation
      exact ⟨after, rfl, v.trans visible, d.trans visible, p.trans position,
        ⟨by rw [v]; exact admitted.1, by rw [d]; exact admitted.1, by rw [p]; exact admitted.2.2⟩⟩

/-- Every successful repair acknowledgement returns exactly the acknowledged
records and leaves both byte images equal to their complete encoding. Host
scripts are arbitrary; failures, blocking and record-limit returns cannot
supply a successful Some result. The initial image is stable, as after reopen. -/
theorem repair_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (trace : Result.ReadyPrefix (repair_log file maxRecords) (fileEnv env file before frame)
      (.ok (.Ok (some returned), returnedFile)) world) :
    returnedFile = file ∧ returned.val = values ∧ ∃ after,
      world = fileEnv env file after frame ∧ after.visible = disk (logBytes values) ∧
      after.durable = disk (logBytes values) ∧ Admitted after := by
  have valid : Valid before := ⟨admitted.1, by rw [stable], admitted.2.2⟩
  simp only [repair_log, monadLift_self] at trace
  obtain ⟨output, middle, completed, continuation⟩ := trace.bind_returns
  obtain ⟨reply, scannedFile⟩ := output
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok parsed =>
      obtain ⟨tail, short, contents⟩ := log_image_shape values before.visible visible
      obtain ⟨fileEqual, scanned, rfl, v, d, scannedValid, recovered⟩ :=
        Record.RepairReturnProperties.recover_returns file env frame before values tail maxRecords
          parsed scannedFile middle separate valid stable contents short completed
      subst scannedFile
      dsimp only at continuation
      by_cases capped : parsed.len = maxRecords
      · simp only [capped, ↓reduceIte, NativeM.ok] at continuation
        cases continuation
      · have notCapped : parsed.val.length ≠ maxRecords.val := by
          intro equal
          apply capped
          apply UScalar.eq_of_val_eq
          simpa only [alloc.vec.Vec.len, Usize.ofNatCore, UScalar.ofNatCore_val_eq] using equal
        have full : parsed.val = values := recovered.resolve_left notCapped
        rw [if_neg capped] at continuation
        simp only [alloc.vec.Vec.len, full, NativeM.lift, Result.ok_bind] at continuation
        have capacity : values.length ≤ 262144 := by
          have prefixBound := visible.1.1
          have visibleBound := admitted.1
          simp only [disk, ← ByteArray.size_data, List.size_toArray, List.length_map,
            logBytes_length, limit] at prefixBound visibleBound
          omega
        have cast : UScalar.cast .U64 (Usize.ofNatCore values.length (by scalar_tac)) =
            U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega) := by
          apply UScalar.eq_of_val_eq
          have small : values.length < 18446744073709551616 := by omega
          simp [UScalar.cast_val_eq, Usize.ofNatCore, U64.ofNatCore]
          omega
        rw [cast] at continuation
        have multiply : U64.checked_mul (U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega)) 4#u64 =
            some (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega)) := by
          apply NativeM.checkedMulU64_of_val
          simp [U64.ofNatCore, Nat.mul_comm]
        rw [multiply] at continuation
        obtain ⟨result, finalWorld, phaseTrace, continuation⟩ := continuation.bind_returns
        cases result with
        | Err error =>
            simp only [NativeM.ok] at continuation
            cases continuation
        | Ok returnedUnit =>
            cases returnedUnit
            have scannedAdmitted : Admitted scanned :=
              ⟨scannedValid.1, by rw [d, ← v]; exact scannedValid.1, scannedValid.2.2⟩
            obtain ⟨after, rfl, finalVisible, finalDurable, _, finalAdmitted⟩ :=
              resize_then_sync_returns file _ env frame scanned finalWorld separate scannedAdmitted phaseTrace
            have resized : resize scanned.visible (4 * values.length) = disk (logBytes values) := by
              rw [v, contents]
              simpa only [logBytes_length] using resize_prefix (logBytes values) tail
            simp only [U64.ofNatCore, UScalar.ofNatCore_val_eq, resized] at finalVisible finalDurable
            simp only [NativeM.ok] at continuation
            cases continuation
            exact ⟨rfl, full, after, rfl, finalVisible, finalDurable, finalAdmitted⟩

/-- This acknowledgement postcondition holds for every successful terminal raw
runtime execution. It does not select a host script or assert termination. -/
theorem repair_run_acknowledges (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Record.RepairImageInvariant.Reply)
    (executed : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_log file maxRecords) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok (some returned), returnedFile))) :
    returnedFile = file ∧ returned.val = values ∧ ∃ after,
      last = .start (fileEnv env file after frame) (.ok (.Ok (some returned), returnedFile)) elapsed ∧
      after.visible = disk (logBytes values) ∧ after.durable = disk (logBytes values) ∧ Admitted after := by
  have safe := Record.RepairImageInvariant.repair_log_invariant env file frame values before maxRecords
    separate admitted stable visible
  obtain ⟨world, trace, ending⟩ := safe.run_returns elapsed executed terminal
  obtain ⟨identity, records, after, rfl, v, d, valid⟩ :=
    repair_returns file env frame before values maxRecords returned returnedFile world
      separate admitted stable visible trace
  exact ⟨identity, records, after, ending, v, d, valid⟩

/-- After any successful runtime acknowledgement every admitted crash image is
exactly the repaired log, including its truncated length. The old partial tail
cannot reappear through an admitted persistence choice. -/
theorem acknowledged_crash_image (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Record.RepairImageInvariant.Reply)
    (executed : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_log file maxRecords) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok (some returned), returnedFile)))
    (mask : ByteArray) (image : Image)
    (captured : crashImage file mask (Record.RepairImageInvariant.snapshot env.currentPid last) = some image) :
    returned.val = values ∧ image.bytes = disk (logBytes values) ∧ image.bytes.size ≤ limit := by
  obtain ⟨identity, records, after, rfl, v, d, valid⟩ := repair_run_acknowledges env file frame before values
    maxRecords returned returnedFile separate admitted stable visible elapsed events last executed terminal
  simp only [Record.RepairImageInvariant.snapshot] at captured
  unfold crashImage at captured
  rw [lookup_admitted env file after frame separate valid] at captured
  change (persist after.durable after.visible mask).bind
    (fun bytes => some (⟨bytes, (fileEnv env file after frame).nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, accepted, equal⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj equal
  rw [v, d] at accepted
  have exactImage := persist_same (disk (logBytes values)) mask bytes accepted
  exact ⟨records, exactImage, by simpa only [exactImage, v] using valid.1⟩

/-- Two successful actual repairs under arbitrary host scripts return the same
records and exact durable image. This is conditional idempotence: neither call
is assumed to terminate or to succeed under an arbitrary script. -/
theorem repair_twice (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (firstLimit secondLimit : Usize) (first second : alloc.vec.Vec U16)
    (firstFile secondFile : NativeFile) (middle world : Environment)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (firstTrace : Result.ReadyPrefix (repair_log file firstLimit) (fileEnv env file before frame)
      (.ok (.Ok (some first), firstFile)) middle)
    (secondTrace : Result.ReadyPrefix (repair_log firstFile secondLimit) middle
      (.ok (.Ok (some second), secondFile)) world) :
    first.val = values ∧ second.val = values ∧ secondFile = file ∧ ∃ after,
      world = fileEnv env file after frame ∧ after.visible = disk (logBytes values) ∧
      after.durable = disk (logBytes values) ∧ Admitted after := by
  obtain ⟨identity, firstRecords, scanned, rfl, v, d, valid⟩ := repair_returns file env frame before values
    firstLimit first firstFile middle separate admitted stable visible firstTrace
  subst firstFile
  have complete : LogImage values scanned.visible := by
    rw [v]
    simpa only [List.append_nil] using log_image values [] (by simp)
  obtain ⟨identity, secondRecords, after, worldEqual, v, d, valid⟩ :=
    repair_returns file env frame scanned values secondLimit second secondFile world separate valid
      (d.trans v.symm) complete secondTrace
  exact ⟨firstRecords, secondRecords, identity, after, worldEqual, v, d, valid⟩

end Record.RepairAcknowledgement
