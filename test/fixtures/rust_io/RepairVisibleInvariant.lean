module
public import Record.RecoveryVisibleFrame
public import Record.AppendPrefixInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairVisibleInvariant
variable [heapLayout : Record.Properties.HeapLayout]
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.ResizeProperties Record.CrashProperties Record.LogProperties Record.RepairCrashProperties
  Record.IntegrityProperties Record.RepairAcknowledgement Record.AppendPrefixInvariant

private theorem invariant_at_state (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (state : State)
    (separate : Separate file frame) (admitted : Admitted state)
    (kept : PrefixInvariant env file frame head (fileEnv env file state frame)) :
    Prefix head state.visible ∧ Prefix head state.durable := by
  obtain ⟨actual,equal,valid,v,d⟩ := kept
  have same := congrArg (lookup file) equal
  rw [lookup_admitted env file actual frame separate valid,
    lookup_admitted env file state frame separate admitted] at same
  cases Option.some.inj same
  exact ⟨v,d⟩

/-- Every actual successful repair retains the known records and synchronizes
both images to a size covering them. Later bytes may encode further complete
records, malformed records, or a partial tail. They are not assumed to be short.
This theorem does not classify all additional returned values or prove progress. -/
theorem repair_returns_prefix (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (tail : List U8)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (admitted : Admitted before)
    (contents : before.visible = disk (logBytes values ++ tail))
    (trace : Result.ReadyPrefix (repair_log file maxRecords) (fileEnv env file before frame)
      (.ok (.Ok (some returned), returnedFile)) world) :
    returnedFile = file ∧ (∃ suffix, returned.val = values ++ suffix) ∧ ∃ after,
      world = fileEnv env file after frame ∧ after.visible = after.durable ∧ Prefix (disk (logBytes values)) after.visible ∧
      after.visible.size = 4 * returned.val.length ∧ Admitted after := by
  simp only [repair_log, monadLift_self] at trace
  obtain ⟨output, middle, completed, continuation⟩ := trace.bind_returns
  obtain ⟨reply, scannedFile⟩ := output
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok parsed =>
      obtain ⟨fileEqual, scanned, rfl, v, scannedValid, consumed, recovered⟩ :=
        Record.RecoveryVisibleFrame.recover_returns_prefix file env frame before values tail maxRecords
          parsed scannedFile middle separate admitted contents completed
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
        obtain ⟨suffix,full⟩ := recovered.resolve_left notCapped
        rw [ite_eq_right capped] at continuation
        simp only [alloc.vec.Vec.len, NativeM.lift, Result.ok_bind] at continuation
        have capacity : parsed.val.length ≤ 262144 := by
          have := scannedValid.2.2
          simp only [limit] at this
          omega
        have oldBound : 4 * values.length ≤ 4 * parsed.val.length := by
          simp only [full,List.length_append]
          omega
        have headPresent : Prefix (disk (logBytes values)) before.visible := by
          rw [contents]
          exact prefix_append _ _
        have cast : UScalar.cast .U64 (Usize.ofNatCore parsed.val.length (by scalar_tac)) =
            U64.ofNatCore parsed.val.length (by simp only [UScalarTy.numBits]; omega) := by
          apply UScalar.eq_of_val_eq
          have small : parsed.val.length < 18446744073709551616 := by omega
          simp [UScalar.cast_val_eq, Usize.ofNatCore, U64.ofNatCore]
          omega
        rw [cast] at continuation
        have multiply : U64.checked_mul (U64.ofNatCore parsed.val.length (by simp only [UScalarTy.numBits]; omega)) 4#u64 =
            some (U64.ofNatCore (4 * parsed.val.length) (by simp only [UScalarTy.numBits]; omega)) := by
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
            obtain ⟨after, rfl, finalVisible, finalDurable, _, finalAdmitted⟩ :=
              resize_then_sync_returns file _ env frame scanned finalWorld separate scannedValid phaseTrace
            have retained : Prefix (disk (logBytes values)) (resize scanned.visible (4 * parsed.val.length)) := by
              apply Record.AppendPrefixInvariant.resize_preserves_prefix
              · rw [v]; exact headPresent
              · simpa only [disk,← ByteArray.size_data,List.size_toArray,List.length_map,logBytes_length] using oldBound
            simp only [U64.ofNatCore,UScalar.ofNatCore_val_eq] at finalVisible finalDurable
            simp only [NativeM.ok] at continuation
            cases continuation
            refine ⟨rfl,⟨suffix,full⟩,after,rfl,finalVisible.trans finalDurable.symm,?_,?_,finalAdmitted⟩
            · rw [finalVisible]; exact retained
            · rw [finalVisible]
              simp [resize,← ByteArray.size_data]
              omega

/-- Every ready prefix of actual Rust repair preserves known acknowledged
records before an arbitrary suffix. Completion is not required; reads, truncation,
synchronization, errors, blocking and persistence choices retain actual state. -/
theorem repair_log_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State) (maxRecords : Usize)
    (separate : Separate file frame) (admitted : Admitted before)
    (durable : Prefix (disk (logBytes values)) before.durable) (visible : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (PrefixInvariant env file frame (disk (logBytes values)))
      (repair_log file maxRecords) (fileEnv env file before frame) := by
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
      obtain ⟨fileEqual, after, worldEqual, v, afterValid, consumed, parsed⟩ :=
        Record.RecoveryVisibleFrame.recover_returns_prefix file env frame before values tail maxRecords
          returned returnedFile midway separate admitted contents completed
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
        obtain ⟨afterVisible,afterDurable⟩ := invariant_at_state env file frame _ after separate afterValid initial
        have kept := resize_invariant env file frame (disk (logBytes values)) after
          (U64.ofNatCore (4 * returned.val.length) (by simp only [UScalarTy.numBits]; omega))
          separate afterValid afterVisible afterDurable (by simpa only [U64.ofNatCore,UScalar.ofNatCore_val_eq,disk,← ByteArray.size_data,List.size_toArray,List.length_map,Record.LogProperties.logBytes_length] using oldBound)
        apply kept.bind
        intro result world trace
        cases result <;> exact .ok _ _ _ (kept _ _ trace).1

/-- Actual repair and append preserve every old acknowledgement at every ready
prefix, including failures and incomplete operations. No new success is assumed. -/
theorem repair_append_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (values : List U16) (before : State)
    (maximum : Usize) (value : U16) (separate : Separate file frame) (valid : Admitted before)
    (durable : Prefix (disk (logBytes values)) before.durable) (image : Prefix (disk (logBytes values)) before.visible) :
    Result.NativeInvariant (PrefixInvariant env file frame (disk (logBytes values)))
      (repair_and_append file maximum value) (fileEnv env file before frame) := by
  rw [Record.RepairWriterProperties.repair_append_contract]
  have prefixSafe := repair_log_invariant env file frame values before maximum
    separate valid durable image
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
          obtain ⟨identity,_,_⟩ := repair_returns_prefix file env frame before values tail maximum
            records repairedFile world separate valid contents trace
          subst repairedFile
          obtain ⟨state,rfl,admitted,v,d⟩ := kept
          exact append_invariant env file frame _ state value separate admitted v d

end Record.RepairVisibleInvariant
