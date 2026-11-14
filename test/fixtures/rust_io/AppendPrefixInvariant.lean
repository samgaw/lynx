module
public import Record.RepairAppendAcknowledgement
public import Record.EncodedPrefixRecovery
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.AppendPrefixInvariant
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties Record.LogProperties
  Record.ResizeProperties Record.RepairCrashProperties Record.RecoveryScanInvariant
  Record.EncodedPrefixRecovery

/-- Overwriting at or after an acknowledged prefix cannot change its bytes. -/
theorem overwrite_prefix (head old data : ByteArray) (position count : Nat)
    (present : Prefix head old) (afterHead : head.size ≤ position) (bounded : count ≤ data.size) :
    Prefix head (overwrite old position data count) := by
  have oldLength := present.1
  have size := overwrite_size old data position count bounded
  refine ⟨by split at size <;> omega, ?_⟩
  intro i inside
  by_cases zero : count = 0
  · simpa only [overwrite, zero, ↓reduceIte] using present.2 i inside
  · have oldBound : i < old.size := by have := present.1; omega
    have outputBound : i < (overwrite old position data count).size := by
      have := present.1; split at size <;> omega
    have takeBound : i < min position old.size := by omega
    have same : (overwrite old position data count)[i]! = old[i]! := by
      rw [getElem!_pos _ i outputBound, getElem!_pos _ i oldBound]
      simp [overwrite, zero, ByteArray.getElem_eq_getElem_data, List.getElem_append_left,
        takeBound]
    exact same.trans (present.2 i inside)

/-- Resizing beyond the acknowledged prefix preserves it, including extension. -/
theorem resize_preserves_prefix (head data : ByteArray) (length : Nat)
    (present : Prefix head data) (afterHead : head.size ≤ length) :
    Prefix head (resize data length) := by
  have size : (resize data length).size = length := by
    simp [resize, ← ByteArray.size_data]
    omega
  refine ⟨by omega, ?_⟩
  intro i inside
  have dataBound : i < data.size := by have := present.1; omega
  have outputBound : i < (resize data length).size := by omega
  have takeBound : i < min length data.size := by omega
  have same : (resize data length)[i]! = data[i]! := by
    rw [getElem!_pos _ i outputBound, getElem!_pos _ i dataBound]
    simp [resize, ByteArray.getElem_eq_getElem_data, List.getElem_append_left,
      takeBound]
  exact same.trans (present.2 i inside)

/-- One actual file cell and all unrelated frame/environment fields survive. -/
@[expose] def PrefixInvariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (world : Environment) : Prop :=
  ∃ state, world = fileEnv env file state frame ∧ Admitted state ∧
    Prefix head state.visible ∧ Prefix head state.durable

private theorem seek_preserves (before : State) (origin : SeekFrom)
    (reply : core.result.Result U64 NativeIoError) (after : State)
    (head : ByteArray) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (step : seekStep before origin = some (reply, after)) :
    Admitted after ∧ Prefix head after.visible ∧ Prefix head after.durable := by
  unfold seekStep at step
  cases chosen : action "seek" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, count, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases accepted : persist before.durable before.visible mask with
      | none => simp [accepted] at step
      | some data =>
          simp only [accepted, Option.bind_some] at step
          have sizes := persist_lengths _ _ _ _ accepted
          have image := persist_prefix _ _ _ _ _ durable visible accepted
          cases success
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl, rfl⟩ := step
            exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega, valid.2.2⟩,
              visible, image⟩
          · simp only [↓reduceIte] at step
            split at step
            · contradiction
            · simp only [Option.some.injEq, Prod.mk.injEq] at step
              obtain ⟨rfl, rfl⟩ := step
              exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega,
                by dsimp; omega⟩, visible, image⟩

private theorem write_preserves (before : State) (value : U16)
    (reply : core.result.Result Usize NativeIoError) (after : State) (head : ByteArray)
    (valid : Admitted before) (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (position : head.size ≤ before.position)
    (step : writeStep before (payload value) = some (reply, after)) :
    Admitted after ∧ Prefix head after.visible ∧ Prefix head after.durable := by
  have original := step
  have payloadLength : (payload value).val.length = 4 := by simp [payload, layout]
  unfold writeStep at step
  simp only [payloadLength, show ¬ 4 > limit by decide, decide_false, Bool.false_or, ↓reduceIte] at step
  cases chosen : action "write" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, count, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases success
      · cases accepted : persist before.durable before.visible mask with
        | none => simp [accepted] at step
        | some bytes =>
            simp only [accepted, Option.bind_some] at step
            obtain ⟨rfl, rfl⟩ := step
            have sizes := persist_lengths _ _ _ _ accepted
            exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega, valid.2.2⟩,
              visible, persist_prefix _ _ _ _ _ durable visible accepted⟩
      · simp only [↓reduceIte] at step
        split at step
        · rename_i bounded
          split at step
          · contradiction
          · cases accepted : persist before.durable
                (overwrite before.visible before.position (bytes (payload value)) count) mask with
            | none => rw [accepted] at step; contradiction
            | some persistedImage =>
                simp only [accepted, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
                obtain ⟨rfl, rfl⟩ := step
                have nextVisible := overwrite_prefix head before.visible (bytes (payload value))
                  before.position count visible position (by simpa [bytes_size, payloadLength] using bounded)
                have nextValid := (Record.AppendAcknowledgement.write_shape before value _ _ valid original).2.2.2
                exact ⟨nextValid, nextVisible, persist_prefix _ _ _ _ _ durable nextVisible accepted⟩
        · contradiction

private theorem resize_preserves (before : State) (length : U64)
    (reply : core.result.Result Unit NativeIoError) (after : State) (head : ByteArray)
    (valid : Admitted before) (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (lengthBound : head.size ≤ length.val)
    (step : setLenStep before length = some (reply, after)) :
    Admitted after ∧ Prefix head after.visible ∧ Prefix head after.durable := by
  have resizedPrefix := resize_preserves_prefix head before.visible length.val visible lengthBound
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
        · simp only [Bool.false_eq_true, ↓reduceIte] at step
          cases accepted : persist before.durable before.visible mask with
          | none => simp [accepted] at step
          | some data =>
              simp only [accepted, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
              obtain ⟨rfl, rfl⟩ := step
              have sizes := persist_lengths _ _ _ _ accepted
              exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega, valid.2.2⟩,
                visible, persist_prefix _ _ _ _ _ durable visible accepted⟩
        · simp only [↓reduceIte] at step
          split at step
          · contradiction
          · cases accepted : persist before.durable (resize before.visible length.val) mask with
            | none => simp [accepted] at step
            | some data =>
                simp only [accepted, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
                obtain ⟨rfl, rfl⟩ := step
                have resizedSize : (resize before.visible length.val).size = length.val := by
                  simp [resize, ← ByteArray.size_data]; omega
                have sizes := persist_lengths _ _ _ _ accepted
                have lengthFits : length.val ≤ limit := by omega
                exact ⟨⟨by simpa only [resizedSize] using lengthFits,
                  by dsimp; have := valid.2.1; omega, valid.2.2⟩,
                  resizedPrefix, persist_prefix _ _ _ _ _ durable resizedPrefix accepted⟩

private theorem sync_preserves (before : State)
    (reply : core.result.Result Unit NativeIoError) (after : State) (head : ByteArray)
    (valid : Admitted before) (visible : Prefix head before.visible)
    (durable : Prefix head before.durable)
    (step : syncStep before = some (reply, after)) :
    Admitted after ∧ Prefix head after.visible ∧ Prefix head after.durable := by
  unfold syncStep at step
  cases chosen : action "sync_all" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, value, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases success
      · simp only [Bool.false_eq_true, ↓reduceIte] at step
        cases accepted : persist before.durable before.visible mask with
        | none => simp [accepted] at step
        | some data =>
            simp only [accepted, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl, rfl⟩ := step
            have sizes := persist_lengths _ _ _ _ accepted
            exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega, valid.2.2⟩,
              visible, persist_prefix _ _ _ _ _ durable visible accepted⟩
      · simp only [↓reduceIte] at step
        split at step
        · contradiction
        · simp only [Option.some.injEq, Prod.mk.injEq] at step
          obtain ⟨rfl, rfl⟩ := step
          exact ⟨⟨valid.1, valid.1, valid.2.2⟩, visible, visible⟩

private theorem sync_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (io_core.synchronize file) (fileEnv env file before frame) := by
  have initial : PrefixInvariant env file frame head (fileEnv env file before frame) :=
    ⟨before, rfl, valid, visible, durable⟩
  simp only [io_core.synchronize, monadLift_self, NativeFile.syncAll]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro actual world ready
  unfold pollSync at ready
  rw [lookup_admitted env file before frame separate valid] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases step : syncStep before with
    | none =>
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        exact .error _ _ _ initial
    | some outcome =>
        obtain ⟨reply, after⟩ := outcome
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        rw [store_at env file before after frame separate]
        have kept := sync_preserves before reply after head valid visible durable step
        exact .ok _ _ _ ⟨after, rfl, kept⟩

/-- The actual resize/sync implementation preserves acknowledged records at
all prefixes, for every admitted persistence mask and host outcome. -/
theorem resize_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State) (length : U64)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (lengthBound : head.size ≤ length.val) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (resize_then_sync file length) (fileEnv env file before frame) := by
  have initial : PrefixInvariant env file frame head (fileEnv env file before frame) :=
    ⟨before, rfl, valid, visible, durable⟩
  simp only [resize_then_sync, io_core.resize_to, monadLift_self, NativeFile.setLen, Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro actual world ready
  unfold pollSetLen at ready
  rw [no_shared_handle_at env file before frame separate,
    lookup_admitted env file before frame separate valid] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases step : setLenStep before length with
    | none =>
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        simpa only [Result.error_bind] using
          Result.NativeInvariant.error (PrefixInvariant env file frame head) .exhausted _ initial
    | some outcome =>
        obtain ⟨reply, after⟩ := outcome
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        rw [store_at env file before after frame separate]
        simp only [Result.ok_bind]
        have kept := resize_preserves before length reply after head valid visible durable lengthBound step
        cases reply with
        | Err error => exact .ok _ _ _ ⟨after, rfl, kept⟩
        | Ok returnedUnit => exact sync_invariant env file frame head after separate kept.1 kept.2.1 kept.2.2

private theorem seek_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (next : core.result.Result U64 NativeIoError × NativeFile → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (continuation : ∀ reply after, Admitted after → Prefix head after.visible → Prefix head after.durable →
      seekStep before (.end_ 0#i64) = some (reply, after) →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply,file))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (NativeFile.seek file (.end_ 0#i64) >>= next) (fileEnv env file before frame) := by
  have initial : PrefixInvariant env file frame head (fileEnv env file before frame) :=
    ⟨before,rfl,valid,visible,durable⟩
  simp only [NativeFile.seek, Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro actual world ready
  unfold pollSeek at ready
  rw [lookup_admitted env file before frame separate valid] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases step : seekStep before (.end_ 0#i64) with
    | none =>
        simp only [step] at ready
        obtain ⟨rfl,rfl⟩ := ready
        simpa only [Result.error_bind] using Result.NativeInvariant.error _ .exhausted _ initial
    | some output =>
        obtain ⟨reply,after⟩ := output
        simp only [step] at ready
        obtain ⟨rfl,rfl⟩ := ready
        rw [store_at env file before after frame separate]
        simp only [Result.ok_bind]
        have kept := seek_preserves before (.end_ 0#i64) reply after head valid visible durable step
        exact continuation reply after kept.1 kept.2.1 kept.2.2 step

private theorem write_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State) (value : U16)
    (next : core.result.Result Usize NativeIoError × NativeFile → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (position : head.size ≤ before.position)
    (continuation : ∀ reply after, Admitted after → Prefix head after.visible → Prefix head after.durable →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply,file))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (NativeFile.write file (payload value) >>= next) (fileEnv env file before frame) := by
  have initial : PrefixInvariant env file frame head (fileEnv env file before frame) :=
    ⟨before,rfl,valid,visible,durable⟩
  simp only [NativeFile.write, Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro actual world ready
  unfold pollWrite at ready
  rw [lookup_admitted env file before frame separate valid,
    no_shared_handle_at env file before frame separate] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases step : writeStep before (payload value) with
    | none =>
        simp only [step] at ready
        obtain ⟨rfl,rfl⟩ := ready
        simpa only [Result.error_bind] using Result.NativeInvariant.error _ .exhausted _ initial
    | some output =>
        obtain ⟨reply,after⟩ := output
        simp only [step] at ready
        obtain ⟨rfl,rfl⟩ := ready
        rw [store_at env file before after frame separate]
        simp only [Result.ok_bind]
        have kept := write_preserves before value reply after head valid visible durable position step
        exact continuation reply after kept.1 kept.2.1 kept.2.2

/-- Every ready prefix of actual Rust append/rollback retains the acknowledged
bytes in both images, regardless of partial writes, errors, blocked operations,
rollback/sync failure and admitted persistence choices. No new acknowledgement
or successful completion is required. -/
theorem append_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State) (value : U16)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (append_record_or_rollback file value) (fileEnv env file before frame) := by
  rw [Record.RollbackProperties.append_contract]
  apply seek_next_invariant env file frame head before _ separate valid visible durable
  intro reply sought soughtValid soughtVisible soughtDurable seek
  cases reply with
  | Err error => exact .ok _ _ _ ⟨sought,rfl,soughtValid,soughtVisible,soughtDurable⟩
  | Ok start =>
      obtain ⟨startValue,_,soughtPosition,_⟩ := Record.AppendAcknowledgement.seek_end_shape before start sought valid seek
      have startBound : head.size ≤ start.val := by rw [startValue]; exact visible.1
      apply write_next_invariant env file frame head sought value _ separate soughtValid soughtVisible soughtDurable
        (by rw [soughtPosition]; exact visible.1)
      intro reply written writtenValid writtenVisible writtenDurable
      cases reply with
      | Err error => exact .ok _ _ _ ⟨written,rfl,writtenValid,writtenVisible,writtenDurable⟩
      | Ok amount =>
          by_cases complete : amount.val = 4
          · simp only [complete]
            have synced := sync_invariant env file frame head written separate writtenValid writtenVisible writtenDurable
            apply Result.NativeInvariant.bind (computation := NativeFile.syncAll file)
            · simpa only [io_core.synchronize,monadLift_self] using synced
            intro reply world trace
            have kept := (synced _ _ trace).1
            cases reply with
            | Err error => exact .ok _ _ _ kept
            | Ok returnedUnit => cases returnedUnit; exact .ok _ _ _ kept
          · simp only
            have resized := resize_invariant env file frame head written start separate writtenValid
              writtenVisible writtenDurable startBound
            apply Result.NativeInvariant.bind (computation := resize_then_sync file start) resized
            intro reply world trace
            have kept := (resized _ _ trace).1
            cases reply with
            | Err error => exact .ok _ _ _ kept
            | Ok returnedUnit => cases returnedUnit; exact .ok _ _ _ kept

/-- Transfer a proved native prefix invariant to the actual raw runtime
snapshot, including a blocked native wait. No terminal-success premise is used. -/
theorem prefix_run (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (computation : Result α)
    (safe : Result.NativeInvariant (PrefixInvariant env file frame head) computation
      (fileEnv env file before frame))
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config α)
    (run : Concurrent.Run (.start (fileEnv env file before frame) computation elapsed) events last) :
    PrefixInvariant env file frame head (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) := by
  obtain ⟨world,kept,current⟩ := safe.run elapsed run
  rcases current with ⟨residual,rfl⟩ | ⟨residual,rfl⟩
  · exact kept
  · obtain ⟨state,rfl,admitted,v,d⟩ := kept
    have observed : (Concurrent.State.initial (fileEnv env file state frame) elapsed).nativeView env.currentPid =
        fileEnv env file state frame := by
      simp [Concurrent.State.nativeView, Concurrent.State.view, Concurrent.State.process,
        Concurrent.State.initial, fileEnv]
    simpa only [Record.RepairAppendAcknowledgement.snapshot,observed] using
      (show PrefixInvariant env file frame head (fileEnv env file state frame) from
        ⟨state,rfl,admitted,v,d⟩)

/-- The acknowledged prefix survives every raw execution prefix of the actual
append/rollback body, even when the caller never acknowledges a new record. -/
theorem append_prefix_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State) (value : U16)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (append_record_or_rollback file value) elapsed) events last) :
    PrefixInvariant env file frame head (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) := by
  exact prefix_run env file frame head before _
    (append_invariant env file frame head before value separate valid visible durable) elapsed events last run

/-- An admitted crash of any world retaining a common encoded prefix permits
actual capped Rust recovery of that prefix. The suffix remains unconstrained. -/
theorem recover_prefix_image (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (world : Environment)
    (separate : Separate file frame)
    (kept : PrefixInvariant env file frame (disk (logBytes values)) world)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage file mask world = some image) :
    ∃ (capacity : values.length ≤ 262144),
      recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (restarted image (recoveryScript image.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            (scanning image.bytes rest (4 * values.length)) []) := by
  obtain ⟨state,observed,admitted,v,d⟩ := kept
  rw [observed] at captured
  unfold crashImage at captured
  rw [lookup_admitted env file state frame separate admitted] at captured
  change (persist state.durable state.visible mask).bind
    (fun bytes => some (⟨bytes,(fileEnv env file state frame).nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes,persisted,equal⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj equal
  have kept := persist_prefix _ _ _ _ _ d v persisted
  have sizes := persist_lengths _ _ _ _ persisted
  have bounded : bytes.size ≤ limit := by have := admitted.1; have := admitted.2.1; omega
  have capacity : values.length ≤ 262144 := by
    have headBound := kept.1
    simp only [disk,← ByteArray.size_data,List.size_toArray,List.length_map,logBytes_length,limit] at headBound bounded
    omega
  exact ⟨capacity,restart_prefix values _ rest kept bounded capacity⟩

/-- At every crash point, actual bounded Rust recovery can read every old
acknowledged record, without assuming a new acknowledgement or discarding the
possibly complete, partial or malformed unacknowledged suffix. -/
theorem recover_after_append_prefix (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (value : U16)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix (disk (logBytes values)) before.visible)
    (durable : Prefix (disk (logBytes values)) before.durable)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame)
      (append_record_or_rollback file value) elapsed) events last)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage file mask (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) = some image) :
    ∃ (capacity : values.length ≤ 262144),
      recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (restarted image (recoveryScript image.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            (scanning image.bytes rest (4 * values.length)) []) := by
  exact recover_prefix_image env file frame values _ separate
    (append_prefix_invariant env file frame _ before value separate valid visible durable elapsed events last run)
    mask image rest captured

end Record.AppendPrefixInvariant
