module
public import Record.RepairInvariantProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairPrefixRecoveryProperties
open NativeFile Record.RecoveryProperties Record.Properties Record.ResizeProperties Record.RepairCrashProperties
  Record.RepeatedRepairProperties Record.RepairInvariantProperties

/-- Actual Rust repair after a crash at any reachable prefix recovers the record.
This is a safety/resumption contract, not a claim that blocked IO completes. -/
theorem recover_after_prefix (mask : ByteArray) (elapsed : PID → Nat → Nat)
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
  have kept := prefix_image last crashMask image
    (Concurrent.checkInvariant_sound (mask_checked mask elapsed) run) captured
  simpa only [repairScript, complete] using
    restart_repair [13#u16] image .nil 3#usize kept.1 kept.2 (by decide)


set_option maxRecDepth 8192 in
set_option cbv.maxSteps 100000 in
/-- Malformed host persistence choices exhaust verification rather than
acknowledging an actual Rust repair. Prefix safety does not imply completion. -/
theorem malformed_exhausts (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun outcome => match outcome with
      | .error .exhausted => true
      | _ => false) 96
      (.start (initial ⟨#[2, 2, 2, 2]⟩) (repair_log ⟨1⟩ 3#usize) elapsed) = true := by cbv

end Record.RepairPrefixRecoveryProperties
