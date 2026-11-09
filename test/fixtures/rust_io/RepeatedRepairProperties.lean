module
public import Record.RepairCrashProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepeatedRepairProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties

/-- Successful host operations for one actual repair, followed by the caller's
remaining operations. A write acknowledgement alone is never a synchronization. -/
@[expose] def repairScript (data : ByteArray) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask data)
    (reader data (outcome "set_len" true 0 (zeroMask data)
      (outcome "sync_all" true 0 ByteArray.empty rest)) 0).script

/-- Repairing a complete log preserves every record and both byte images.
The cursor ends at the repaired EOF, independently of its initial position. -/
theorem clean_repair (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (bounded : (logBytes values).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values), disk (logBytes values), position,
        repairScript (disk (logBytes values)) rest⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (finished (disk (logBytes values)) rest) frame) := by
  simpa only [repairScript, repaired, finished, List.append_nil] using
    repair_default file env frame values [] rest position maxRecords
      separate (by simp) (by simpa using bounded) offset more

/-- Two calls of the actual extracted repair routine agree on the recovered
records and durable bytes, including when the first call removes a partial tail. -/
theorem repair_idempotent (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val) :
    let retry := repairScript (disk (logBytes values)) rest
    let intermediate := fileEnv env file (repaired values tail retry) frame
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        repairScript (disk (logBytes values ++ tail)) retry⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file), intermediate) ∧
    repair_log file maxRecords intermediate =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (finished (disk (logBytes values)) rest) frame) := by
  dsimp only
  constructor
  · exact repair_default file env frame values tail _ position maxRecords
      separate short bounded offset more
  · apply clean_repair file env frame values rest _ maxRecords separate
    · simp only [List.length_append] at bounded
      omega
    · simpa only [disk, ← ByteArray.size_data, List.size_toArray, List.length_map, List.length_append] using bounded
    · exact more

/-- Relational composition of actual executions. Each successor carries an
execution equation; it cannot be justified by an assumed function contract. -/
@[expose] def Repeated (computation : NativeM α) (reply : α) :
    Nat → Environment → Environment → Prop
  | 0, before, after => before = after
  | count + 1, before, after => ∃ middle,
      computation before = (.ok reply, middle) ∧ Repeated computation reply count middle after

@[expose] def scripts (data : ByteArray) (rest : Term) : Nat → Term
  | 0 => rest
  | count + 1 => repairScript data (scripts data rest count)

/-- Any finite number of successful repeat repairs executes the same actual
Rust implementation, retaining the full log and the caller's unrelated frame. -/
theorem repair_repeated (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16)
    (rest : Term) (count : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (bounded : (logBytes values).length ≤ limit)
    (more : values.length < maxRecords.val) :
    Repeated (repair_log file maxRecords)
      (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file) count
      (fileEnv env file (finished (disk (logBytes values))
        (scripts (disk (logBytes values)) rest count)) frame)
      (fileEnv env file (finished (disk (logBytes values)) rest) frame) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    refine ⟨_, ?_, ih⟩
    apply clean_repair file env frame values _ _ maxRecords separate bounded
    · simpa only [disk, ← ByteArray.size_data, List.size_toArray, List.length_map] using bounded
    · exact more

end Record.RepeatedRepairProperties
