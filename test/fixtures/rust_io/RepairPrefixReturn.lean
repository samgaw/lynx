module
public import Record.RecoveryFrame
public import Record.AppendPrefixInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairPrefixReturn
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.ResizeProperties Record.CrashProperties Record.LogProperties Record.RepairCrashProperties
  Record.IntegrityProperties Record.RepairAcknowledgement

/-- Every actual successful repair retains the known records and synchronizes
both images to a size covering them. Later bytes may encode further complete
records, malformed records, or a partial tail. They are not assumed to be short.
This theorem does not classify all additional returned values or prove progress. -/
theorem repair_returns_prefix (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (tail : List U8)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (contents : before.visible = disk (logBytes values ++ tail))
    (trace : Result.ReadyPrefix (repair_log file maxRecords) (fileEnv env file before frame)
      (.ok (.Ok (some returned), returnedFile)) world) :
    returnedFile = file ∧ (∃ suffix, returned.val = values ++ suffix) ∧ ∃ after,
      world = fileEnv env file after frame ∧ after.visible = after.durable ∧ Prefix (disk (logBytes values)) after.visible ∧
      after.visible.size = 4 * returned.val.length ∧ Admitted after := by
  have valid : Valid before := ⟨admitted.1, by rw [stable], admitted.2.2⟩
  simp only [repair_log, monadLift_self] at trace
  obtain ⟨output, middle, completed, continuation⟩ := trace.bind_returns
  obtain ⟨reply, scannedFile⟩ := output
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok parsed =>
      obtain ⟨fileEqual, scanned, rfl, v, d, scannedValid, consumed, recovered⟩ :=
        Record.RecoveryFrame.recover_returns_prefix file env frame before values tail maxRecords
          parsed scannedFile middle separate valid stable contents completed
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
            have scannedAdmitted : Admitted scanned :=
              ⟨scannedValid.1, by rw [d, ← v]; exact scannedValid.1, scannedValid.2.2⟩
            obtain ⟨after, rfl, finalVisible, finalDurable, _, finalAdmitted⟩ :=
              resize_then_sync_returns file _ env frame scanned finalWorld separate scannedAdmitted phaseTrace
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

end Record.RepairPrefixReturn
