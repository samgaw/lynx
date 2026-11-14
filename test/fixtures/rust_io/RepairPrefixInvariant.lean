module
public import Record.RecoveryPrefixInvariant
public import Record.RepairPrefixReturn
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairPrefixInvariant
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.CrashProperties Record.LogProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.AppendPrefixInvariant

/-- Every ready prefix of actual Rust repair preserves known acknowledged
records before an arbitrary suffix. Completion is not required; reads, truncation,
synchronization, errors, blocking and persistence choices retain actual state. -/
theorem repair_log_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maxRecords : Usize)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (PrefixInvariant env file frame (disk (logBytes values)))
      (repair_log file maxRecords) (fileEnv env file before frame) := by
  have durable : Prefix (disk (logBytes values)) before.durable := stable ▸ visible
  have valid : Valid before := ⟨admitted.1, by rw [stable], admitted.2.2⟩
  have safe := Record.RecoveryPrefixInvariant.recover_log_invariant env file frame (disk (logBytes values)) before maxRecords separate admitted visible durable
  simp only [repair_log, monadLift_self]
  apply safe.bind
  intro output midway completed
  have initial := (safe _ _ completed).1
  obtain ⟨reply, returnedFile⟩ := output
  cases reply with
  | Err error => exact .ok _ _ _ initial
  | Ok returned =>
      obtain ⟨tail, contents⟩ := Record.EncodedPrefixRecovery.prefix_shape values before.visible visible
      obtain ⟨fileEqual, after, worldEqual, v, d, afterValid, consumed, parsed⟩ :=
        Record.RecoveryFrame.recover_returns_prefix file env frame before values tail maxRecords
          returned returnedFile midway separate valid stable contents completed
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
        obtain ⟨suffix,extension⟩ := parsed.resolve_left notCapped
        have oldBound : 4 * values.length ≤ 4 * returned.val.length := by
          simp only [extension,List.length_append]
          omega
        rw [ite_eq_right capped]
        simp only [alloc.vec.Vec.len, NativeM.lift]
        have capacity : returned.val.length ≤ 262144 := by
          have := afterValid.2.2
          simp only [limit] at this
          omega
        have cast : UScalar.cast .U64 (Usize.ofNatCore returned.val.length (by scalar_tac)) =
            U64.ofNatCore returned.val.length (by simp only [UScalarTy.numBits]; omega) := by
          apply UScalar.eq_of_val_eq
          have small : returned.val.length < 18446744073709551616 := by omega
          simp [UScalar.cast_val_eq, Usize.ofNatCore, U64.ofNatCore]
          omega
        rw [cast]
        simp only [Result.ok_bind]
        have multiply : U64.checked_mul (U64.ofNatCore returned.val.length (by simp only [UScalarTy.numBits]; omega)) 4#u64 =
            some (U64.ofNatCore (4 * returned.val.length) (by simp only [UScalarTy.numBits]; omega)) := by
          apply NativeM.checkedMulU64_of_val
          simp [U64.ofNatCore, Nat.mul_comm]
        rw [multiply]
        have afterAdmitted : Admitted after := ⟨afterValid.1, by rw [d, ← v]; exact afterValid.1, afterValid.2.2⟩
        have afterVisible : Prefix (disk (logBytes values)) after.visible := v ▸ visible
        have afterDurable : Prefix (disk (logBytes values)) after.durable := d ▸ visible
        have kept := resize_invariant env file frame (disk (logBytes values)) after
          (U64.ofNatCore (4 * returned.val.length) (by simp only [UScalarTy.numBits]; omega))
          separate afterAdmitted afterVisible afterDurable (by simpa only [U64.ofNatCore,UScalar.ofNatCore_val_eq,disk,← ByteArray.size_data,List.size_toArray,List.length_map,Record.LogProperties.logBytes_length] using oldBound)
        apply kept.bind
        intro result world trace
        cases result <;> exact .ok _ _ _ (kept _ _ trace).1

/-- No successful return is assumed: every finite raw execution prefix,
including the runtime configuration of a blocked wait, retains both prefixes. -/
theorem repair_prefix_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maximum : Usize)
    (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (visible : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame) (repair_log file maximum) elapsed) events last) :
    PrefixInvariant env file frame (disk (logBytes values))
      (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) := by
  exact prefix_run env file frame _ before _
    (repair_log_invariant env file frame values before maximum separate valid stable visible)
    elapsed events last run

/-- Every admitted crash at any actual repair prefix permits actual capped
Rust recovery of the known records, with an unrestricted unexamined suffix. -/
theorem recover_after_repair_prefix (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maximum : Usize)
    (separate : Separate file frame) (valid : Admitted before)
    (stable : before.durable = before.visible) (visible : Prefix (disk (logBytes values)) before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile))
    (run : Concurrent.Run (.start (fileEnv env file before frame) (repair_log file maximum) elapsed) events last)
    (mask : ByteArray) (crash : Image) (rest : Term)
    (captured : crashImage file mask (Record.RepairAppendAcknowledgement.snapshot env.currentPid last) = some crash) :
    ∃ (capacity : values.length ≤ 262144),
      recover_log ⟨crash.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (restarted crash (recoveryScript crash.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨crash.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨crash.highWater + 1⟩
            (scanning crash.bytes rest (4 * values.length)) []) := by
  exact recover_prefix_image env file frame values _ separate
    (repair_prefix_invariant env file frame values before maximum separate valid stable visible elapsed events last run)
    mask crash rest captured

end Record.RepairPrefixInvariant
