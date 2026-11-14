module
public import Record.RepairWriterProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.AppendAcknowledgement
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties Record.LogProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.RecoveryScanInvariant

private theorem seek_end_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result U64 NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (NativeFile.seek file (.end_ 0#i64)) (fileEnv env file before frame)
      (.ok (reply, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      seekStep before (.end_ 0#i64) = some (reply, after) := by
  simp only [NativeFile.seek] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollSeek at ready
          rw [lookup_admitted env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : seekStep before (.end_ 0#i64) with
            | none => simp [step] at ready
            | some output =>
                obtain ⟨reply, after⟩ := output
                simp only [step] at ready
                obtain ⟨rfl, rfl⟩ := ready
                exact ⟨rfl, after, store_at env file before after frame separate, rfl⟩

/-- A successful end-relative seek returns the actual visible length and cursor. -/
theorem seek_end_shape (before : State) (offset : U64) (after : State)
    (valid : Admitted before) (step : seekStep before (.end_ 0#i64) = some (.Ok offset, after)) :
    offset.val = before.visible.size ∧ after.visible = before.visible ∧
      after.position = before.visible.size ∧ Admitted after := by
  unfold seekStep at step
  cases chosen : action "seek" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, value, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases persisted : persist before.durable before.visible mask with
      | none => simp [persisted] at step
      | some bytes =>
          simp only [persisted, Option.bind_some] at step
          cases success
          · simp at step
          · simp only [↓reduceIte] at step
            split at step
            · contradiction
            · simp only [Option.some.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at step
              obtain ⟨rfl, rfl⟩ := step
              have sizes := persist_lengths _ _ _ _ persisted
              have vb := valid.1
              have db := valid.2.1
              exact ⟨by simp [U64.ofNatCore, seekTarget], rfl, by simp [seekTarget],
                vb, by dsimp; omega, by simpa [seekTarget] using vb⟩

private theorem write_returns (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result Usize NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (NativeFile.write file (payload value)) (fileEnv env file before frame)
      (.ok (reply, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      writeStep before (payload value) = some (reply, after) := by
  simp only [NativeFile.write] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollWrite at ready
          rw [lookup_admitted env file before frame separate valid,
            no_shared_handle_at env file before frame separate] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : writeStep before (payload value) with
            | none => simp [step] at ready
            | some output =>
                obtain ⟨reply, after⟩ := output
                simp only [step] at ready
                obtain ⟨rfl, rfl⟩ := ready
                exact ⟨rfl, after, store_at env file before after frame separate, rfl⟩

/-- Successful writes retain the actual count, resulting bytes and cursor bounds. -/
theorem write_shape (before : State) (value : U16) (amount : Usize) (after : State)
    (valid : Admitted before)
    (step : writeStep before (payload value) = some (.Ok amount, after)) :
    amount.val ≤ 4 ∧
      after.visible = overwrite before.visible before.position (bytes (payload value)) amount.val ∧
      after.position = before.position + amount.val ∧ Admitted after := by
  have payloadLength : (payload value).val.length = 4 := by simp [payload, layout]
  unfold writeStep at step
  simp only [payloadLength, show ¬ 4 > limit by decide, decide_false, Bool.false_or, ↓reduceIte] at step
  cases chosen : action "write" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, count, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases success
      · cases persisted : persist before.durable before.visible mask with
        | none => simp [persisted] at step
        | some persistedImage => simp [persisted] at step
      · simp only [↓reduceIte] at step
        split at step
        · rename_i bounded
          split at step
          · contradiction
          · rename_i fits
            cases persisted : persist before.durable
                (overwrite before.visible before.position (bytes (payload value)) count) mask with
            | none => rw [persisted] at step; contradiction
            | some persistedImage =>
                simp only [persisted, Option.bind_some, Option.some.injEq, Prod.mk.injEq,
                  core.result.Result.Ok.injEq] at step
                obtain ⟨rfl, rfl⟩ := step
                have sizes := persist_lengths _ _ _ _ persisted
                have vb := valid.1
                have db := valid.2.1
                have positionFits : before.position + count ≤ limit := by
                  have noOverflow : ¬ before.position + count > limit := by simpa using fits
                  omega
                have overwriteSize := overwrite_size before.visible (bytes (payload value)) before.position count
                  (by simpa [bytes_size, payload, layout] using bounded)
                simp only [Usize.ofNatCore, UScalar.ofNatCore_val_eq]
                refine ⟨bounded, trivial, trivial, ?_, ?_, ?_⟩
                · dsimp; split at overwriteSize <;> omega
                · dsimp; split at overwriteSize <;> omega
                · dsimp; omega
        · contradiction

/-- Every actual successful return distinguishes a durable append from a durable
rollback. Host scripts, masks, cursors and the initial durable image vary freely
within the bounded independent-file admission. No success or termination is assumed. -/
theorem append_returns (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (accepted : Bool)
    (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (append_record_or_rollback file value) (fileEnv env file before frame)
      (.ok (.Ok accepted, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = (if accepted then overwrite before.visible before.visible.size (bytes (payload value)) 4 else before.visible) ∧
      after.durable = after.visible ∧ Admitted after := by
  rw [Record.RollbackProperties.append_contract] at trace
  obtain ⟨⟨seekReply, seekFile⟩, middle, soughtTrace, continuation⟩ := trace.bind_returns
  obtain ⟨identity, sought, rfl, seekStep⟩ := seek_end_returns file env frame before seekReply seekFile middle
    separate valid soughtTrace
  subst seekFile
  cases seekReply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok start =>
      obtain ⟨startValue, soughtVisible, soughtPosition, soughtValid⟩ := seek_end_shape before start sought valid seekStep
      obtain ⟨⟨writeReply, writeFile⟩, middle, writtenTrace, continuation⟩ := continuation.bind_returns
      obtain ⟨identity, written, rfl, writeStep⟩ := write_returns file value env frame sought writeReply writeFile middle
        separate soughtValid writtenTrace
      subst writeFile
      cases writeReply with
      | Err error =>
          simp only [NativeM.ok] at continuation
          cases continuation
      | Ok amount =>
          obtain ⟨bounded, writtenVisible, writtenPosition, writtenValid⟩ := write_shape sought value amount written soughtValid writeStep
          by_cases complete : amount.val = 4
          · simp only [complete] at continuation
            obtain ⟨syncReply, middle, syncedTrace, continuation⟩ := continuation.bind_returns
            cases syncReply with
            | Err error =>
                simp only [NativeM.ok] at continuation
                cases continuation
            | Ok returnedUnit =>
                cases returnedUnit
                obtain ⟨after, rfl, visible, durable, position⟩ :=
                  Record.RepairAcknowledgement.synchronize_returns file env frame written middle separate writtenValid syncedTrace
                simp only [NativeM.ok] at continuation
                cases continuation
                refine ⟨rfl, after, rfl, ?_, ?_, ?_, ?_, ?_⟩
                · simpa only [↓reduceIte, writtenVisible, soughtVisible, soughtPosition, complete] using visible
                · rw [durable, visible]
                · rw [visible]; exact writtenValid.1
                · rw [durable]; exact writtenValid.1
                · rw [position]; exact writtenValid.2.2
          · simp only at continuation
            obtain ⟨resizeReply, middle, resizedTrace, continuation⟩ := continuation.bind_returns
            cases resizeReply with
            | Err error =>
                simp only [NativeM.ok] at continuation
                cases continuation
            | Ok returnedUnit =>
                cases returnedUnit
                obtain ⟨after, rfl, visible, durable, position, afterValid⟩ :=
                  Record.RepairAcknowledgement.resize_then_sync_returns file start env frame written middle
                    separate writtenValid resizedTrace
                simp only [NativeM.ok] at continuation
                cases continuation
                have resized : resize written.visible start.val = before.visible := by
                  rw [writtenVisible, soughtVisible, soughtPosition, startValue]
                  exact Record.RollbackProperties.truncate_append _ _ _
                exact ⟨rfl, after, rfl, by simpa only [Bool.false_eq_true, ↓reduceIte, resized] using visible,
                  by rw [durable, visible], afterValid⟩

private theorem resize_fragment (file : NativeFile) (length : U64) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (resize_then_sync file length) env := by
  simp only [resize_then_sync, io_core.resize_to, monadLift_self]
  apply Result.NativeInvariant.bind (computation := NativeFile.setLen file length)
  · simp only [NativeFile.setLen]
    apply Result.NativeInvariant.wait _ _ _ trivial
    intro actual after _
    cases actual with
    | ok value => exact .ok _ _ _ trivial
    | error exception => exact .error _ _ _ trivial
  intro reply world _
  cases reply with
  | Err error => exact .ok _ _ _ trivial
  | Ok returnedUnit =>
      cases returnedUnit
      simp only [io_core.synchronize, monadLift_self, NativeFile.syncAll]
      apply Result.NativeInvariant.wait _ _ _ trivial
      intro actual after _
      cases actual with
      | ok value => exact .ok _ _ _ trivial
      | error exception => exact .error _ _ _ trivial

/-- Native-only confinement is separate from the durable return contract. It
retains actual trace evidence even for malformed state, blocking and failure. -/
theorem append_fragment (file : NativeFile) (value : U16) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (append_record_or_rollback file value) env := by
  rw [Record.RollbackProperties.append_contract]
  apply Result.NativeInvariant.bind (computation := NativeFile.seek file (.end_ 0#i64))
  · simp only [NativeFile.seek]
    apply Result.NativeInvariant.wait _ _ _ trivial
    intro actual after _
    cases actual with
    | ok value => exact .ok _ _ _ trivial
    | error exception => exact .error _ _ _ trivial
  intro output world _
  obtain ⟨reply, file⟩ := output
  cases reply with
  | Err error => exact .ok _ _ _ trivial
  | Ok start =>
      apply Result.NativeInvariant.bind (computation := NativeFile.write file (payload value))
      · simp only [NativeFile.write]
        apply Result.NativeInvariant.wait _ _ _ trivial
        intro actual after _
        cases actual with
        | ok value => exact .ok _ _ _ trivial
        | error exception => exact .error _ _ _ trivial
      intro output world _
      obtain ⟨reply, file⟩ := output
      cases reply with
      | Err error => exact .ok _ _ _ trivial
      | Ok amount =>
          by_cases complete : amount.val = 4
          · simp only [complete]
            apply Result.NativeInvariant.bind (computation := NativeFile.syncAll file)
            · simp only [NativeFile.syncAll]
              apply Result.NativeInvariant.wait _ _ _ trivial
              intro actual after _
              cases actual with
              | ok value => exact .ok _ _ _ trivial
              | error exception => exact .error _ _ _ trivial
            intro reply after _
            cases reply <;> exact .ok _ _ _ trivial
          · simp only
            apply Result.NativeInvariant.bind (computation := resize_then_sync file start)
            · exact resize_fragment file start world
            intro reply after _
            cases reply <;> exact .ok _ _ _ trivial

/-- Every successful raw runtime completion, rather than only a selected ready
trace or host script, satisfies the actual append/rollback acknowledgement. -/
theorem append_run_acknowledges (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (accepted : Bool) (returnedFile : NativeFile)
    (separate : Separate file frame) (valid : Admitted before)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (append_record_or_rollback file value) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok accepted, returnedFile))) :
    returnedFile = file ∧ ∃ after,
      last = .start (fileEnv env file after frame) (.ok (.Ok accepted, returnedFile)) elapsed ∧
      after.visible = (if accepted then overwrite before.visible before.visible.size (bytes (payload value)) 4 else before.visible) ∧
      after.durable = after.visible ∧ Admitted after := by
  obtain ⟨world, trace, ending⟩ := (append_fragment file value _).run_returns elapsed run terminal
  obtain ⟨identity, after, rfl, visible, durable, admitted⟩ :=
    append_returns file value env frame before accepted returnedFile world separate valid trace
  exact ⟨identity, after, ending, visible, durable, admitted⟩

end Record.AppendAcknowledgement
