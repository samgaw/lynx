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

open Record.RepairCrashProperties

/-- Host operations up to an interrupted synchronization after actual repair.
The resize mask may retain any persistence outcome admitted by the file model. -/
@[expose] def interruptionScript (data mask : ByteArray) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask data)
    (reader data (outcome "set_len" true 0 mask (.cons (.atom "blocked") rest)) 0).script

@[expose] def interruptedEnv (before : Image) (values : List U16) (tail : List U8)
    (durable : ByteArray) (rest : Term) : Environment :=
  fileEnv {} ⟨before.highWater + 1⟩
    (pendingRepair values tail durable (.cons (.atom "blocked") rest)) []

/-- One observed synchronization interruption and power loss. Every edge includes
an execution equation for the extracted Rust body, a blocked sync observation,
and the actual crash-image relation. No successful repair is assumed. -/
@[expose] def InterruptedRepair
    (implementation : NativeFile → Usize → NativeM
      (core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile))
    (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) (before after : Image) : Prop :=
  ∃ (tail : List U8) (mask durable crashMask : ByteArray) (rest : Term),
    before.bytes = disk (logBytes values ++ tail) ∧ tail.length < 4 ∧
    persist before.bytes (disk (logBytes values)) mask = some durable ∧
    implementation ⟨before.highWater + 1⟩ maxRecords
      (restarted before (interruptionScript before.bytes mask rest)) =
      (io_core.synchronize ⟨before.highWater + 1⟩ >>=
        repairReply ⟨before.highWater + 1⟩ (alloc.vec.Vec.from values (by scalar_tac))).run
          (interruptedEnv before values tail durable rest) ∧
    pollSync ⟨before.highWater + 1⟩ (interruptedEnv before values tail durable rest) = none ∧
    crashImage ⟨before.highWater + 1⟩ crashMask
      (interruptedEnv before values tail durable rest) = some after

/-- Every admitted pair of resize/crash choices has its actual implementation
edge; this is not an assumption that a desired execution exists. -/
theorem interrupt_admitted (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) (before after : Image) (tail : List U8)
    (mask durable crashMask : ByteArray) (rest : Term)
    (contents : before.bytes = disk (logBytes values ++ tail)) (short : tail.length < 4)
    (bounded : before.bytes.size ≤ limit) (more : values.length < maxRecords.val)
    (accepted : persist before.bytes (disk (logBytes values)) mask = some durable)
    (captured : crashImage ⟨before.highWater + 1⟩ crashMask
      (interruptedEnv before values tail durable rest) = some after) :
    InterruptedRepair repair_log values capacity maxRecords before after := by
  have bound : (logBytes values ++ tail).length ≤ limit := by
    simpa [contents, disk, ← ByteArray.size_data] using bounded
  have proof := repair_interrupt ⟨before.highWater + 1⟩ ({} : Environment) [] values tail
    mask durable crashMask rest .nil 0 maxRecords after (by simp [Separate]) short bound
    (by simp [limit]) more (by simpa only [contents] using accepted) captured
  refine ⟨tail, mask, durable, crashMask, rest, contents, short, accepted, ?_, proof.2.1, captured⟩
  simpa only [interruptionScript, restart_as_fileEnv, contents, interruptedEnv] using proof.1

/-- Arbitrarily many interruptions, each restarting with a fresh capability.
The final attempt may still be interrupted: completion is proved separately. -/
@[expose] def RepairCrashes
    (implementation : NativeFile → Usize → NativeM
      (core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile))
    (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) : Nat → Image → Image → Prop
  | 0, before, after => before = after
  | count + 1, before, after => ∃ middle,
      InterruptedRepair implementation values capacity maxRecords before middle ∧
      RepairCrashes implementation values capacity maxRecords count middle after

/-- All allowed persistence choices retain the acknowledged prefix throughout a
finite sequence of interrupted repairs. Volatile offsets/handles are not retained. -/
theorem interruptions_preserve (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) (count : Nat) (before after : Image)
    (shape : LogImage values before.bytes) (bounded : before.bytes.size ≤ limit)
    (trace : RepairCrashes repair_log values capacity maxRecords count before after) :
    LogImage values after.bytes ∧ after.bytes.size ≤ limit := by
  induction count generalizing before with
  | zero => cases trace; exact ⟨shape, bounded⟩
  | succ count ih =>
    obtain ⟨middle, ⟨tail, mask, durable, crashMask, rest, contents, short, accepted,
      _execution, _blocked, captured⟩, remaining⟩ := trace
    have bound : (logBytes values ++ tail).length ≤ limit := by
      simpa [contents, disk, ← ByteArray.size_data] using bounded
    have state := pending_image values tail mask durable (.cons (.atom "blocked") rest)
      short bound (by simpa only [contents] using accepted)
    have kept := crash_log_image ⟨before.highWater + 1⟩ ({} : Environment) []
      _ values crashMask middle (by simp [Separate]) state.1 state.2.1 state.2.2 captured
    exact ih middle kept.1 kept.2 remaining

/-- After any finite interrupted sequence, successful host operations let the
actual Rust repair return all acknowledged records and synchronize the tail removal. -/
theorem retry_after_interruptions (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) (count : Nat) (before after : Image) (rest : Term)
    (shape : LogImage values before.bytes) (bounded : before.bytes.size ≤ limit)
    (more : values.length < maxRecords.val)
    (trace : RepairCrashes repair_log values capacity maxRecords count before after) :
    repair_log ⟨after.highWater + 1⟩ maxRecords
      (restarted after (repairScript after.bytes rest)) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨after.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨after.highWater + 1⟩
          ⟨disk (logBytes values), disk (logBytes values), after.bytes.size, rest⟩ []) := by
  have kept := interruptions_preserve values capacity maxRecords count before after shape bounded trace
  exact restart_repair values after rest maxRecords kept.1 kept.2 more

/-- Any finite number of interruptions is possible without favorable persistence:
retain the old durable image each time, while the freshness counter advances. -/
theorem interruptions_witness (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) (count : Nat) (before : Image)
    (shape : LogImage values before.bytes) (bounded : before.bytes.size ≤ limit)
    (more : values.length < maxRecords.val) :
    ∃ after, RepairCrashes repair_log values capacity maxRecords count before after ∧
      after.bytes = before.bytes ∧ after.highWater = before.highWater + count := by
  induction count generalizing before with
  | zero => exact ⟨before, rfl, rfl, by omega⟩
  | succ count ih =>
    obtain ⟨tail, short, contents⟩ := log_image_shape values before.bytes shape
    let middle : Image := ⟨before.bytes, before.highWater + 1⟩
    have accepted := persist_keep_old before.bytes (disk (logBytes values))
    have bound : (logBytes values ++ tail).length ≤ limit := by
      simpa [contents, disk, ← ByteArray.size_data] using bounded
    have state := pending_image values tail (zeroMask before.bytes) before.bytes
      (.cons (.atom "blocked") .nil) short bound (by simpa only [contents] using accepted)
    have captured : crashImage ⟨before.highWater + 1⟩ (zeroMask before.bytes)
        (interruptedEnv before values tail before.bytes .nil) = some middle := by
      unfold interruptedEnv crashImage
      rw [lookup_admitted ({} : Environment) ⟨before.highWater + 1⟩ _ []
        (by simp [Separate]) state.1]
      simp [pendingRepair, persist_keep_old, fileEnv, middle]
    have step := interrupt_admitted values capacity maxRecords before middle tail
      (zeroMask before.bytes) before.bytes (zeroMask before.bytes) .nil contents short
      bounded more accepted captured
    obtain ⟨after, remaining, bytes, watermark⟩ := ih middle shape bounded
    exact ⟨after, ⟨middle, step, remaining⟩, bytes, by dsimp [middle] at watermark; omega⟩

end Record.RepeatedRepairProperties
