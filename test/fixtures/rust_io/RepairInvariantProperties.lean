module
public import Record.RepeatedRepairProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairInvariantProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.RepeatedRepairProperties

abbrev Reply := core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile

@[expose] def complete : ByteArray := disk (logBytes [13#u16])
@[expose] def original : ByteArray := disk (logBytes [13#u16] ++ [7#u8])
@[expose] def padded : ByteArray := disk (logBytes [13#u16] ++ [0#u8])

@[expose] def retained (data : ByteArray) : Bool :=
  data.data == complete.data || data.data == original.data || data.data == padded.data

@[expose] def world : Concurrent.Config Reply → Environment
  | .start env .. => env
  | .running state .. => state.nativeView []

@[expose] def safe (config : Concurrent.Config Reply) : Bool :=
  match lookup ⟨1⟩ (world config) with
  | some state => retained state.visible && retained state.durable && decide (state.position ≤ limit)
  | none => false

@[expose] def initial (mask : ByteArray) : Environment :=
  fileEnv {} ⟨1⟩ ⟨original, original, 0, interruptionScript original mask .nil⟩ []

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
set_option cbv.maxSteps 32000000 in
/-- Each reachable configuration, not just the blocked terminal state, retains
its record before and after the actual Rust scan, resize and sync attempt. -/
theorem old_image_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 96
      (.start (initial (zeroMask original)) (repair_log ⟨1⟩ 3#usize) elapsed) = true := by cbv

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
set_option cbv.maxSteps 32000000 in
theorem truncated_image_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 96
      (.start (initial (zeroMask complete)) (repair_log ⟨1⟩ 3#usize) elapsed) = true := by cbv

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
set_option cbv.maxSteps 32000000 in
theorem padded_image_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 96
      (.start (initial ⟨_root_.Array.replicate 5 1⟩) (repair_log ⟨1⟩ 3#usize) elapsed) = true := by cbv

theorem retained_shape (data : ByteArray) (kept : retained data = true) :
    LogImage [13#u16] data ∧ data.size ≤ limit := by
  simp only [retained, Bool.or_eq_true, beq_iff_eq] at kept
  rcases kept with (kept | kept) | kept
  all_goals have equal := ByteArray.ext kept; subst data
  · exact ⟨by simpa only [complete, List.append_nil] using log_image [13#u16] [] (by decide), by decide⟩
  · exact ⟨log_image _ _ (by decide), by decide⟩
  · exact ⟨log_image _ _ (by decide), by decide⟩

/-- Any allowed power loss at a checked prefix retains the complete record.
The crash mask is arbitrary; no successful Rust return is needed. -/
theorem prefix_image (config : Concurrent.Config Reply) (mask : ByteArray) (image : Image)
    (checked : safe config = true)
    (captured : crashImage ⟨1⟩ mask (world config) = some image) :
    LogImage [13#u16] image.bytes ∧ image.bytes.size ≤ limit := by
  unfold safe at checked
  split at checked
  · rename_i state found
    simp only [Bool.and_eq_true, decide_eq_true_eq] at checked
    have visible := retained_shape state.visible checked.1.1
    have durable := retained_shape state.durable checked.1.2
    unfold crashImage at captured
    rw [found] at captured
    change (persist state.durable state.visible mask).bind
      (fun bytes => some (⟨bytes, (world config).nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨bytes, persisted, equal⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj equal
    have sizes := persist_lengths _ _ _ _ persisted
    exact ⟨persist_log_image _ _ _ _ _ durable.1 visible.1 persisted,
      by have := visible.2; have := durable.2; dsimp; omega⟩
  · contradiction

/-- Actual Rust repair after a crash at any reachable prefix recovers the record.
This is a safety/resumption contract, not a claim that blocked IO completes. -/
theorem recover_after_prefix (mask : ByteArray) (elapsed : PID → Nat → Nat)
    (selected : mask = zeroMask original ∨ mask = zeroMask complete ∨
      mask = ⟨_root_.Array.replicate 5 1⟩)
    (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (run : Concurrent.Run
      (.start (initial mask) (repair_log ⟨1⟩ 3#usize) elapsed) events last)
    (crashMask : ByteArray) (image : Image)
    (captured : crashImage ⟨1⟩ crashMask (world last) = some image) :
    repair_log ⟨image.highWater + 1⟩ 3#usize
      (restarted image (repairScript image.bytes .nil)) =
      (.ok (.Ok (some (alloc.vec.Vec.from [13#u16] (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨complete, complete, image.bytes.size, .nil⟩ []) := by
  have checked : Concurrent.checkInvariant safe 96
      (.start (initial mask) (repair_log ⟨1⟩ 3#usize) elapsed) = true := by
    rcases selected with rfl | rfl | rfl
    · exact old_image_checked elapsed
    · exact truncated_image_checked elapsed
    · exact padded_image_checked elapsed
  have kept := prefix_image last crashMask image
    (Concurrent.checkInvariant_sound checked run) captured
  simpa only [repairScript, complete] using
    restart_repair [13#u16] image .nil 3#usize kept.1 kept.2 (by decide)

end Record.RepairInvariantProperties
