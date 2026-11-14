module
public import Record.ConcurrentRepairInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.ConcurrentRepairRecovery
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties Record.RecoveryProperties
  Record.ResizeProperties Record.RepairCrashProperties Record.RepeatedRepairProperties
  Record.ConcurrentRepairInvariant

private theorem bytes_equal (left right : ByteArray) (equal : (left == right) = true) : left = right := by
  change (left.data == right.data) = true at equal
  exact ByteArray.ext (by simpa only [beq_iff_eq] using equal)

/-- The combined raw invariant yields terminal acceptance without a second
exploration or a terminal-only reduction of the intermediate-state property. -/
theorem terminal_accepted (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start initial callers elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) : accepted last = true := by
  have kept := Concurrent.checkInvariant_sound (prefixes_checked elapsed) run
  simp only [safe, Bool.and_eq_true] at kept
  simpa only [terminal.successors_eq_nil, List.isEmpty_nil, Bool.not_true,
    Bool.false_or] using kept.2

private theorem prefix_images (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start initial callers elapsed) events last) :
    ∃ file, NativeFile.lookup ⟨2⟩ (snapshot last) = some file ∧
      LogImage [13#u16] file.visible ∧ LogImage [13#u16] file.durable ∧
      file.visible.size ≤ limit ∧ file.durable.size ≤ limit := by
  have kept := Concurrent.checkInvariant_sound (prefixes_checked elapsed) run
  simp only [safe, Bool.and_eq_true] at kept
  have retained : retained last = true := kept.1
  unfold Record.ConcurrentRepairInvariant.retained at retained
  split at retained
  · rename_i file found
    simp only [Bool.and_eq_true, Bool.or_eq_true] at retained
    have shape : ∀ data, data = torn ∨ data = complete → LogImage [13#u16] data ∧ data.size ≤ limit := by
      intro data choices
      rcases choices with rfl | rfl
      · exact ⟨log_image [13#u16] [7#u8] (by decide), by decide⟩
      · exact ⟨by simpa only [List.append_nil, Record.ConcurrentRepairInvariant.complete] using log_image [13#u16] [] (by decide), by decide⟩
    have v := shape file.visible (retained.1.elim (fun equal => .inl (bytes_equal _ _ equal)) (fun equal => .inr (bytes_equal _ _ equal)))
    have d := shape file.durable (retained.2.elim (fun equal => .inl (bytes_equal _ _ equal)) (fun equal => .inr (bytes_equal _ _ equal)))
    exact ⟨file, found, v.1, d.1, v.2, d.2⟩
  · contradiction

/-- Crashes at every raw prefix of two overlapping actual repairs retain the
acknowledged record. A successful fresh actual repair removes any retained
partial tail, independently of which caller acquired the mutex first. -/
theorem recover_after_prefix (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start initial callers elapsed) events last)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (snapshot last) = some image) :
    repair_log ⟨image.highWater + 1⟩ 3#usize (restarted image (repairScript image.bytes rest)) =
      (.ok (.Ok (some (alloc.vec.Vec.from [13#u16] (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨disk (logBytes [13#u16]), disk (logBytes [13#u16]), image.bytes.size, rest⟩ []) := by
  obtain ⟨file, found, v, d, vb, db⟩ := prefix_images elapsed events last run
  unfold crashImage at captured
  rw [found] at captured
  change (persist file.durable file.visible mask).bind
    (fun bytes => some (⟨bytes, (snapshot last).nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj equal
  have shape := persist_log_image [13#u16] _ _ _ _ d v persisted
  have sizes := persist_lengths _ _ _ _ persisted
  have bound : bytes.size ≤ limit := by omega
  exact restart_repair [13#u16] _ rest 3#usize shape bound (by decide)

/-- After both repairs acknowledged, every admitted crash image is the exact
complete log, not the old torn length. Actual retry returns that same record. -/
theorem terminal_recovery (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start initial callers elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (snapshot last) = some image) :
    image.bytes = complete ∧
      repair_log ⟨image.highWater + 1⟩ 3#usize (restarted image (repairScript image.bytes rest)) =
        (.ok (.Ok (some (alloc.vec.Vec.from [13#u16] (by scalar_tac))), ⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            ⟨disk (logBytes [13#u16]), disk (logBytes [13#u16]), image.bytes.size, rest⟩ []) := by
  have accepted := terminal_accepted elapsed events last outcome run terminal
  have recovered := recover_after_prefix elapsed events last run mask image rest captured
  refine ⟨?_, recovered⟩
  unfold Record.ConcurrentRepairInvariant.accepted at accepted
  split at accepted
  · rename_i file output found
    simp only [Bool.and_eq_true] at accepted
    unfold crashImage at captured
    rw [found] at captured
    change (persist file.durable file.visible mask).bind
      (fun bytes => some (⟨bytes, (snapshot last).nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj equal
    rw [bytes_equal _ _ accepted.1.1, bytes_equal _ _ accepted.1.2] at persisted
    exact Record.RecoveryProperties.persist_same complete mask bytes persisted
  · contradiction

end Record.ConcurrentRepairRecovery
