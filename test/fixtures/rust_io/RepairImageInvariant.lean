module
public import Record.RepairReturnProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairImageInvariant
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.CrashProperties Record.LogProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.RecoveryScanInvariant

private theorem resize_image (values : List U16) (data : ByteArray) (length : U64)
    (image : LogImage values data) (size : length.val = 4 * values.length) :
    resize data length.val = disk (logBytes values) := by
  obtain ⟨tail, _, rfl⟩ := log_image_shape values data image
  simpa only [size, logBytes_length] using resize_prefix (logBytes values) tail

private theorem resize_preserves (before : State) (length : U64)
    (reply : core.result.Result Unit NativeIoError) (after : State) (values : List U16)
    (valid : Admitted before) (visible : LogImage values before.visible)
    (durable : LogImage values before.durable) (size : length.val = 4 * values.length)
    (step : setLenStep before length = some (reply, after)) :
    Admitted after ∧ LogImage values after.visible ∧ LogImage values after.durable := by
  have resized := resize_image values before.visible length visible size
  have headImage : LogImage values (disk (logBytes values)) := by
    simpa only [List.append_nil] using log_image values [] (by simp)
  have headBound : (disk (logBytes values)).size ≤ limit := by
    have := visible.1.1
    have := valid.1
    omega
  unfold setLenStep at step
  split at step
  · contradiction
  · cases chosen : action "set_len" before.script with
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
                visible, persist_log_image _ _ _ _ _ durable visible accepted⟩
        · simp only [↓reduceIte] at step
          split at step
          · contradiction
          · rw [resized] at step
            cases accepted : persist before.durable (disk (logBytes values)) mask with
            | none => simp [accepted] at step
            | some data =>
                simp only [accepted, Option.bind_some, Option.some.injEq, Prod.mk.injEq] at step
                obtain ⟨rfl, rfl⟩ := step
                have sizes := persist_lengths _ _ _ _ accepted
                exact ⟨⟨headBound, by dsimp; have := valid.2.1; omega, valid.2.2⟩,
                  headImage, persist_log_image _ _ _ _ _ durable headImage accepted⟩

private theorem sync_preserves (before : State)
    (reply : core.result.Result Unit NativeIoError) (after : State) (values : List U16)
    (valid : Admitted before) (visible : LogImage values before.visible)
    (durable : LogImage values before.durable)
    (step : syncStep before = some (reply, after)) :
    Admitted after ∧ LogImage values after.visible ∧ LogImage values after.durable := by
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
              visible, persist_log_image _ _ _ _ _ durable visible accepted⟩
      · simp only [↓reduceIte] at step
        split at step
        · contradiction
        · simp only [Option.some.injEq, Prod.mk.injEq] at step
          obtain ⟨rfl, rfl⟩ := step
          exact ⟨⟨valid.1, valid.1, valid.2.2⟩, visible, visible⟩

private theorem sync_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : LogImage values before.visible) (durable : LogImage values before.durable) :
    Result.NativeInvariant (ImageInvariant env file frame values)
      (io_core.synchronize file) (fileEnv env file before frame) := by
  have initial : ImageInvariant env file frame values (fileEnv env file before frame) :=
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
        have kept := sync_preserves before reply after values valid visible durable step
        exact .ok _ _ _ ⟨after, rfl, kept⟩

/-- The actual resize/sync implementation preserves acknowledged records at
all prefixes, for every admitted persistence mask and host outcome. -/
theorem resize_then_sync_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (length : U64)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : LogImage values before.visible) (durable : LogImage values before.durable)
    (size : length.val = 4 * values.length) :
    Result.NativeInvariant (ImageInvariant env file frame values)
      (resize_then_sync file length) (fileEnv env file before frame) := by
  have initial : ImageInvariant env file frame values (fileEnv env file before frame) :=
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
          Result.NativeInvariant.error (ImageInvariant env file frame values) .exhausted _ initial
    | some outcome =>
        obtain ⟨reply, after⟩ := outcome
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        rw [store_at env file before after frame separate]
        simp only [Result.ok_bind]
        have kept := resize_preserves before length reply after values valid visible durable size step
        cases reply with
        | Err error => exact .ok _ _ _ ⟨after, rfl, kept⟩
        | Ok unit => exact sync_invariant env file frame values after separate kept.1 kept.2.1 kept.2.2

/-- Every prefix of actual Rust repair preserves the complete acknowledged
records in both byte images. The initial image is stable, as after reopening;
subsequent reads, resize, sync, errors and tearing choices are arbitrary. -/
theorem repair_log_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maxRecords : Usize)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible) :
    Result.NativeInvariant (ImageInvariant env file frame values)
      (repair_log file maxRecords) (fileEnv env file before frame) := by
  have durable : LogImage values before.durable := stable ▸ visible
  have valid : Valid before := ⟨admitted.1, by rw [stable], admitted.2.2⟩
  have safe := recover_log_invariant env file frame values before maxRecords separate admitted visible durable
  simp only [repair_log, monadLift_self]
  apply safe.bind
  intro output midway completed
  have initial := (safe _ _ completed).1
  obtain ⟨reply, returnedFile⟩ := output
  cases reply with
  | Err error => exact .ok _ _ _ initial
  | Ok returned =>
      obtain ⟨tail, short, contents⟩ := log_image_shape values before.visible visible
      obtain ⟨fileEqual, after, worldEqual, v, d, afterValid, parsed⟩ :=
        Record.RepairReturnProperties.recover_returns file env frame before values tail maxRecords
          returned returnedFile midway separate valid stable contents short completed
      subst returnedFile
      subst midway
      dsimp only
      by_cases capped : returned.len = maxRecords
      · simp only [capped, ↓reduceIte, NativeM.ok]
        exact .ok _ _ _ initial
      · have notCapped : returned.val.length ≠ maxRecords.val := by
          intro equal
          apply capped
          apply UScalar.eq_of_val_eq
          simpa only [alloc.vec.Vec.len, Usize.ofNatCore, UScalar.ofNatCore_val_eq] using equal
        have full : returned.val = values := parsed.resolve_left notCapped
        rw [if_neg capped]
        simp only [alloc.vec.Vec.len, full, NativeM.lift]
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
        rw [cast]
        simp only [Result.ok_bind]
        have multiply : U64.checked_mul (U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega)) 4#u64 =
            some (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega)) := by
          apply NativeM.checkedMulU64_of_val
          simp [U64.ofNatCore, Nat.mul_comm]
        rw [multiply]
        simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
        have afterAdmitted : Admitted after := ⟨afterValid.1, by rw [d, ← v]; exact afterValid.1, afterValid.2.2⟩
        have afterVisible : LogImage values after.visible := v ▸ visible
        have afterDurable : LogImage values after.durable := d ▸ visible
        have kept := resize_then_sync_invariant env file frame values after
          (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega))
          separate afterAdmitted afterVisible afterDurable (by simp [U64.ofNatCore])
        apply kept.bind
        intro result world trace
        cases result <;> exact .ok _ _ _ (kept _ _ trace).1

abbrev Reply := core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile

@[expose] def snapshot (pid : PID) : Concurrent.Config Reply → Environment
  | .start env .. => env
  | .running state .. => state.nativeView pid

/-- Safety at every finite raw runtime prefix, including blocked native waits.
No fairness or successful-completion claim is made. -/
theorem repair_prefix_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maxRecords : Usize)
    (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (executed : Concurrent.Run (.start (fileEnv env file before frame)
      (repair_log file maxRecords) elapsed) events last) :
    ImageInvariant env file frame values (snapshot env.currentPid last) := by
  have safe := repair_log_invariant env file frame values before maxRecords separate valid stable visible
  obtain ⟨world, kept, current⟩ := safe.run elapsed executed
  rcases current with ⟨residual, rfl⟩ | ⟨residual, rfl⟩
  · exact kept
  · obtain ⟨state, rfl, admitted, v, d⟩ := kept
    have observed : (Concurrent.State.initial (fileEnv env file state frame) elapsed).nativeView env.currentPid =
        fileEnv env file state frame := by
      simp [Concurrent.State.nativeView, Concurrent.State.view, Concurrent.State.process,
        Concurrent.State.initial, fileEnv]
    simpa only [snapshot, observed] using
      (show ImageInvariant env file frame values (fileEnv env file state frame) from
        ⟨state, rfl, admitted, v, d⟩)

end Record.RepairImageInvariant
