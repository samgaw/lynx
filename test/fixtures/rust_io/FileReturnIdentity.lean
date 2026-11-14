module
public import Record.RepairAppendPrefixInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.FileReturnIdentity
variable [heapLayout : Record.Properties.HeapLayout]
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.ResizeProperties Record.CrashProperties Record.LogProperties Record.RepairCrashProperties

omit heapLayout in
private theorem seek_frame (before : State) (reply : core.result.Result U64 NativeIoError) (after : State)
    (valid : Valid before) (stable : before.durable = before.visible)
    (step : seekStep before (.start 0#u64) = some (reply,after)) :
    after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after := by
  unfold seekStep at step
  cases chosen : action "seek" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success,count,mask,rest⟩ := choice
      simp only [chosen,Option.bind_eq_bind,Option.bind_some] at step
      cases persisted : persist before.durable before.visible mask with
      | none => simp [persisted] at step
      | some data =>
          have same := persist_same before.visible mask data (by simpa only [stable] using persisted)
          subst data
          simp only [persisted,Option.bind_some] at step
          cases success
          · simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            exact ⟨rfl,rfl,valid.1,le_rfl,valid.2.2⟩
          · simp only [↓reduceIte] at step
            split at step
            · contradiction
            · simp only [Option.some.injEq,Prod.mk.injEq] at step
              obtain ⟨rfl,rfl⟩ := step
              exact ⟨rfl,rfl,valid.1,le_rfl,by simp [seekTarget,limit]⟩

private theorem seek_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result U64 NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (io_core.seek_to file 0#u64) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after := by
  simp only [io_core.seek_to,io_core.seek_from,Record.Extraction.FileModel.seek,NativeFile.seek,monadLift_self] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollSeek at ready
          rw [lookup_at env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : seekStep before (.start 0#u64) with
            | none => simp [step] at ready
            | some outcome =>
                obtain ⟨reply,after⟩ := outcome
                simp only [step] at ready
                obtain ⟨rfl,rfl⟩ := ready
                exact ⟨rfl,after,store_at env file before after frame separate,seek_frame before _ after valid stable step⟩

private theorem loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (accumulated : alloc.vec.Vec U16) (maximum : Usize) (fuel : Nat)
    (reply : core.result.Result (alloc.vec.Vec U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file,values) => recover_log_loop.body maximum file values) fuel (file,accumulated))
      (fileEnv env file before frame) (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after := by
  induction fuel generalizing before accumulated with
  | zero => simp only [NativeM.loopFuel] at trace; cases trace
  | succ fuel ih =>
      rw [NativeM.loopFuel] at trace
      conv at trace => arg 1; arg 1; unfold recover_log_loop.body
      simp only [monadLift_self] at trace
      by_cases advance : accumulated.len < maximum
      · simp only [advance,↓reduceIte,bind_assoc] at trace
        obtain ⟨⟨record,recordFile⟩,middle,recordTrace,continuation⟩ := trace.bind_returns
        obtain ⟨identity,after,rfl,v,d,valid1,_,_⟩ :=
          Record.RecoveryFrame.record_returns file env frame before record recordFile middle separate valid stable recordTrace
        subst recordFile
        cases record with
        | Err error =>
            simp only [NativeM.ok,Result.ok_bind] at continuation
            cases continuation
            exact ⟨rfl,after,rfl,v,d,valid1⟩
        | Ok option =>
            cases option with
            | none =>
                simp only [NativeM.ok,Result.ok_bind] at continuation
                cases continuation
                exact ⟨rfl,after,rfl,v,d,valid1⟩
            | some value =>
                simp only [NativeM.monadLift_eq,Record.Extraction.VectorModel.push_eq] at continuation
                split at continuation
                · simp only [NativeM.fromRust_ok,NativeM.ok,Result.ok_bind] at continuation
                  obtain ⟨identity,final,worldEqual,v2,d2,valid2⟩ := ih (before := after)
                    (accumulated := alloc.vec.Vec.from (accumulated.val ++ [value]) (by scalar_tac))
                    valid1 (d.trans v.symm) continuation
                  exact ⟨identity,final,worldEqual,v2.trans v,d2.trans v,valid2⟩
                · simp [NativeM.fromRust,RustM.fail] at continuation
                  cases continuation
      · simp only [advance,↓reduceIte,NativeM.ok,Result.ok_bind] at trace
        cases trace
        exact ⟨rfl,before,rfl,rfl,stable,valid⟩

/-- Every actual recovery return, including I/O errors, retains the borrowed
file identity and stable images. Blocking, panic and exhaustion do not fabricate
a returned file. Later bytes and host scripts are arbitrary. -/
theorem recover_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (maximum : Usize)
    (reply : core.result.Result (alloc.vec.Vec U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (recover_log file maximum) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after := by
  simp only [recover_log,monadLift_self] at trace
  obtain ⟨⟨sought,soughtFile⟩,middle,seekTrace,continuation⟩ := trace.bind_returns
  obtain ⟨identity,after,rfl,v,d,valid1⟩ := seek_returns file env frame before sought soughtFile middle separate valid stable seekTrace
  subst soughtFile
  cases sought with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
      exact ⟨rfl,after,rfl,v,d,valid1⟩
  | Ok offset =>
      simp only [recover_log_loop,NativeM.loop,monadLift_self] at continuation
      obtain ⟨identity,final,worldEqual,v2,d2,valid2⟩ := loop_returns file env frame after
        (alloc.vec.Vec.new U16) maximum _ reply returnedFile world separate valid1 (d.trans v.symm) continuation
      exact ⟨identity,final,worldEqual,v2.trans v,d2.trans v,valid2⟩

/-- Repair returns the original borrowed file on every Rust result branch,
including failed truncation/sync and capped None. The proof follows the actual
recovery return and actual wrapper, not an assumed borrow contract. -/
theorem repair_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (maximum : Usize)
    (reply : core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (repair_log file maximum) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) : returnedFile = file := by
  simp only [repair_log,monadLift_self] at trace
  obtain ⟨⟨recovered,recoveredFile⟩,middle,recoveryTrace,continuation⟩ := trace.bind_returns
  obtain ⟨identity,_,_,_,_,_⟩ := recover_returns file env frame before maximum recovered recoveredFile middle separate valid stable recoveryTrace
  subst recoveredFile
  cases recovered with
  | Err error => simp only [NativeM.ok] at continuation; cases continuation; rfl
  | Ok values =>
      dsimp only at continuation
      split at continuation
      · simp only [NativeM.ok] at continuation; cases continuation; rfl
      · simp only [NativeM.lift,Result.ok_bind] at continuation
        cases multiplied : U64.checked_mul (UScalar.cast .U64 values.len) 4#u64 with
        | none =>
            simp only [multiplied,NativeM.ok] at continuation
            cases continuation
            rfl
        | some length =>
            simp only [multiplied] at continuation
            change Result.ReadyPrefix (resize_then_sync file length >>= _) middle (.ok (reply,returnedFile)) world at continuation
            obtain ⟨result,middle,_,continuation⟩ := continuation.bind_returns
            cases result <;> simp only [NativeM.ok] at continuation <;> cases continuation <;> rfl

/-- Every append/rollback Rust result retains the file identity, including
seek/write errors, failed rollback and failed synchronization. -/
theorem append_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (value : U16)
    (reply : core.result.Result Bool NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (append_record_or_rollback file value) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) : returnedFile = file := by
  rw [Record.RollbackProperties.append_contract] at trace
  obtain ⟨⟨sought,soughtFile⟩,middle,soughtTrace,continuation⟩ := trace.bind_returns
  obtain ⟨identity,after,rfl,step⟩ := Record.AppendAcknowledgement.seek_end_returns file env frame before
    sought soughtFile middle separate valid soughtTrace
  subst soughtFile
  cases sought with
  | Err error => simp only [NativeM.ok] at continuation; cases continuation; rfl
  | Ok start =>
      have admitted := (Record.AppendAcknowledgement.seek_end_shape before start after valid step).2.2.2
      obtain ⟨⟨written,writtenFile⟩,middle,writeTrace,continuation⟩ := continuation.bind_returns
      obtain ⟨identity,_,_,_⟩ := Record.AppendAcknowledgement.write_returns file value env frame after
        written writtenFile middle separate admitted writeTrace
      subst writtenFile
      cases written with
      | Err error => simp only [NativeM.ok] at continuation; cases continuation; rfl
      | Ok amount =>
          by_cases complete : amount.val = 4
          · simp only [complete] at continuation
            change Result.ReadyPrefix (NativeFile.syncAll file >>= _) middle (.ok (reply,returnedFile)) world at continuation
            obtain ⟨result,_,_,continuation⟩ := continuation.bind_returns
            cases result <;> simp only [NativeM.ok] at continuation <;> cases continuation <;> rfl
          · simp only at continuation
            change Result.ReadyPrefix (resize_then_sync file start >>= _) middle (.ok (reply,returnedFile)) world at continuation
            obtain ⟨result,_,_,continuation⟩ := continuation.bind_returns
            cases result <;> simp only [NativeM.ok] at continuation <;> cases continuation <;> rfl

/-- The composed caller retains the borrowed file on every Rust return.
In particular an I/O error cannot supply a different file to guard release. -/
theorem repair_append_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (maximum : Usize) (value : U16)
    (reply : core.result.Result Bool NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (admitted : Admitted before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (repair_and_append file maximum value) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) : returnedFile = file := by
  rw [Record.RepairWriterProperties.repair_append_contract] at trace
  obtain ⟨⟨repaired,repairedFile⟩,middle,repairedTrace,continuation⟩ := trace.bind_returns
  have valid : Valid before := ⟨admitted.1,by rw [stable],admitted.2.2⟩
  have identity := repair_returns file env frame before maximum repaired repairedFile middle separate valid stable repairedTrace
  subst repairedFile
  cases repaired with
  | Err error => simp only [NativeM.ok] at continuation; cases continuation; rfl
  | Ok option =>
      cases option with
      | none => simp only [NativeM.ok] at continuation; cases continuation; rfl
      | some records =>
          have emptyPrefix : Prefix (disk (logBytes [])) before.visible := by
            constructor
            · simp [disk,logBytes,← ByteArray.size_data]
            · intro i inside; simp [disk,logBytes,← ByteArray.size_data] at inside
          have safe := Record.RepairPrefixInvariant.repair_log_invariant env file frame [] before maximum
            separate admitted stable emptyPrefix
          obtain ⟨after,rfl,valid1,_,_⟩ := (safe _ _ repairedTrace).1
          exact append_returns file env frame after value reply returnedFile world separate valid1 continuation

end Record.FileReturnIdentity
