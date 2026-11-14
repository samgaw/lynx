module
public import Record.RepairWriterProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.EncodedPrefixRecovery
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.LogProperties Record.ResizeProperties Record.RepairCrashProperties

/-- A complete encoded prefix can have an arbitrary suffix, including another
complete or torn unacknowledged record. No short-tail assumption is made. -/
theorem prefix_shape (values : List U16) (data : ByteArray)
    (admittedPrefix : Prefix (disk (logBytes values)) data) :
    ∃ tail : List U8, data = disk (logBytes values ++ tail) := by
  let head := disk (logBytes values)
  change Prefix head data at admittedPrefix
  have equal : data.data.toList.take head.size = head.data.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, _root_.Array.length_toList, ← ByteArray.size_data]
      exact Nat.min_eq_left admittedPrefix.1
    · intro i hi hj
      have inside : i < head.size := by simpa only [_root_.Array.length_toList, ← ByteArray.size_data] using hj
      have bytes := admittedPrefix.2 i inside
      rw [getElem!_pos data i (by have := admittedPrefix.1; omega), getElem!_pos head i inside] at bytes
      simpa only [List.getElem_take, _root_.Array.getElem_toList, ByteArray.getElem_eq_getElem_data] using bytes
  let tail := (data.data.toList.drop head.size).map byteValue
  refine ⟨tail, ?_⟩
  have reconstruct := List.take_append_drop head.size data.data.toList
  rw [equal] at reconstruct
  have headRoundtrip : head.data.toList.map byteValue = logBytes values := by
    simp [head, disk, List.map_map, Function.comp_def, byte_roundtrip]
  have decoded := congrArg (List.map byteValue) reconstruct
  simp only [List.map_append, headRoundtrip] at decoded
  rw [← disk_roundtrip data, ← decoded]

/-- Every admitted persistence choice retains a prefix common to both images,
without restricting the number or validity of records following that prefix. -/
theorem persist_prefix (head old visible mask result : ByteArray)
    (oldPrefix : Prefix head old) (visiblePrefix : Prefix head visible)
    (accepted : persist old visible mask = some result) : Prefix head result := by
  have sizes := persist_lengths old visible mask result accepted
  refine ⟨by have := oldPrefix.1; have := visiblePrefix.1; omega, ?_⟩
  intro i inside
  rw [persist_at old visible mask result accepted i (by have := oldPrefix.1; have := visiblePrefix.1; omega)]
  split
  · exact visiblePrefix.2 i inside
  · exact oldPrefix.2 i inside

/-- The actual parser returns a caller-bounded complete prefix without reading
or repairing its arbitrary suffix. Every read comes from actual encoded bytes. -/
theorem recover_prefix (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (data : ByteArray)
    (rest : Term) (position : Nat) (separate : Separate file frame)
    (bounded : data.size ≤ limit) (offset : position ≤ limit)
    (admittedPrefix : Prefix (disk (logBytes values)) data) (capacity : values.length ≤ 262144) :
    recover_log file (Usize.ofNatCore values.length (by scalar_tac))
      (fileEnv env file ⟨data, data, position, recoveryScript data rest⟩ frame) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        fileEnv env file (scanning data rest (4 * values.length)) frame) := by
  obtain ⟨tail, rfl⟩ := prefix_shape values data admittedPrefix
  apply recover_log_records file env frame _ (scanning (disk (logBytes values ++ tail)) rest 0) _ values _ separate
  · exact ⟨bounded, le_rfl, offset⟩
  · simp [blocked, recoveryScript, outcome]
  · simpa [scanning, recoveryScript, sought] using seek_start
      (⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        recoveryScript (disk (logBytes values ++ tail)) rest⟩ : State)
      0#u64 (zeroMask (disk (logBytes values ++ tail))) (disk (logBytes values ++ tail)) _
      (by simp [limit]) (action_outcome _ _ _ _ _) (persist_zero _)
  · simpa only [List.nil_append, List.length_nil, Nat.zero_add] using
      scanning_records values [] tail rest (by simpa [disk, ← ByteArray.size_data] using bounded)
  · simp [Usize.ofNatCore]
  · exact capacity

/-- Fresh admitted reopening of a crash image recovers the selected complete
prefix through the actual cross-crate Rust reader, even with unacknowledged bytes. -/
theorem restart_prefix (values : List U16) (image : Image) (rest : Term)
    (admittedPrefix : Prefix (disk (logBytes values)) image.bytes)
    (bounded : image.bytes.size ≤ limit) (capacity : values.length ≤ 262144) :
    recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          (scanning image.bytes rest (4 * values.length)) []) := by
  rw [restart_as_fileEnv]
  exact recover_prefix _ _ [] values image.bytes rest 0 (by simp [Separate]) bounded
    (by simp [limit]) admittedPrefix capacity

end Record.EncodedPrefixRecovery
