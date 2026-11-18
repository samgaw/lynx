module
public import Record.MixedRepairRecovery
public import Record.MixedRepairWitness
public import Record.TornSyncChains
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.MixedRepairChains
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (contents call environment)
open Record.TornSyncFailure (withTail tail_forms)
open Record.TornSyncRecovery (names script cold registered repaired reopens_captured_image)
open Record.MixedRepairScripts (start)
open Record.MixedRepairRecovery (reopens_after_prefix_crash)
open Record.TornSyncChains (JournalImage Reopen admitError)

structure AdmittedMasks (left : Bool) (tail : List UInt8) where
  closeSucceeds : Bool
  resizeMask : ByteArray
  syncMask : ByteArray
  closeMask : ByteArray
  resized : ByteArray
  synchronized : ByteArray
  closed : ByteArray
  resize : persist (withTail left tail) (contents left) resizeMask = some resized
  sync : persist resized (contents left) syncMask = some synchronized
  close : persist synchronized (contents left) closeMask = some closed

@[expose] def started (counter : Nat) (left : Bool) (tail : List UInt8)
    (masks : AdmittedMasks left tail) : Environment :=
  start counter left tail masks.resizeMask masks.syncMask masks.closeMask masks.closeSucceeds

@[expose] def bootScript (counter : Nat) (left : Bool) (tail : List UInt8)
    (masks : AdmittedMasks left tail) : Term :=
  (namespaceSnapshot (started counter left tail masks)).map NamespaceSnapshot.script |>.getD .nil

set_option maxRecDepth 8192 in
/-- The modeled failure receives a new error owner after the image restarts. -/
theorem boot_from_image (counter : Nat) (left : Bool) (tail : List UInt8)
    (short : tail.length < 4) (masks : AdmittedMasks left tail) (positive : 1 ≤ counter) :
    (restartFilesystem ⟨names, [(1, withTail left tail)], counter⟩
      (bootScript counter left tail masks)).map admitError =
      some (started counter left tail masks) := by
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    cases left <;> cbv

/-- The scheduler may stop at any prefix of the admitted Rustler call.
The next attempted recovery can use only the captured filesystem image. -/
@[expose] def InterruptedAttempt (reopen : Reopen) (left : Bool)
    (before after : FilesystemImage) : Prop :=
  ∃ (tail : List UInt8) (masks : AdmittedMasks left tail) (boot : Environment)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (chosen : Names) (crashMasks : List (Nat × ByteArray)),
    tail.length < 4 ∧ before = ⟨names, [(1, withTail left tail)], before.highWater⟩ ∧
    (restartFilesystem before (bootScript before.highWater left tail masks)).map admitError =
      some boot ∧
    Concurrent.Run (.start boot (call reopen 3#u32) elapsed) events last ∧
    filesystemCrashImage chosen crashMasks (environment last) = some after

inductive InterruptedAttempts (reopen : Reopen) (left : Bool) :
    Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : InterruptedAttempts reopen left 0 image image
  | next : InterruptedAttempt reopen left before middle →
      InterruptedAttempts reopen left count middle after →
      InterruptedAttempts reopen left (count + 1) before after

private theorem one_attempt (left : Bool) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (interrupted : InterruptedAttempt __TRY_REOPEN__ left before after) :
    JournalImage left after ∧ before.highWater ≤ after.highWater := by
  obtain ⟨_, _, _, positive⟩ := safe
  obtain ⟨tail, masks, boot, elapsed, events, last, chosen, crashMasks, short, sameImage,
    restarted, ran, crash⟩ := interrupted
  have next := boot_from_image before.highWater left tail short masks positive
  have same : boot = started before.highWater left tail masks := by
    rw [sameImage] at restarted
    simpa only [next, Option.some.injEq] using restarted.symm
  rw [same] at ran
  obtain ⟨bytes, recorded, advance, shape, _, _⟩ :=
    reopens_after_prefix_crash before.highWater left masks.closeSucceeds tail short masks.resizeMask
      masks.syncMask masks.closeMask masks.resized masks.synchronized masks.closed masks.resize
      masks.sync masks.close positive elapsed (fun _ _ => 0) events last ran chosen crashMasks after crash
  exact ⟨⟨bytes, recorded, shape, Nat.le_trans positive advance⟩, advance⟩

/-- Arbitrarily many interruptions preserve both acknowledged records and
never lower the reference allocator's high-water mark. -/
theorem repeated_prefix_crashes (left : Bool) (count : Nat) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (attempts : InterruptedAttempts __TRY_REOPEN__ left count before after) :
    JournalImage left after ∧ before.highWater ≤ after.highWater := by
  induction attempts with
  | zero => exact ⟨safe, le_rfl⟩
  | @next before middle count after attempt rest ih =>
    obtain ⟨safeMiddle, advance⟩ := one_attempt left before middle safe attempt
    obtain ⟨safeAfter, later⟩ := ih safeMiddle
    exact ⟨safeAfter, Nat.le_trans advance later⟩

/-- The actual typed NIF repairs the image of the last interrupted attempt
and returns a new readable and writable resource for the same inode. -/
theorem reopens_after_repeated_prefix_crashes (left : Bool) (count : Nat) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (attempts : InterruptedAttempts __TRY_REOPEN__ left count before after)
    (elapsed : PID → Nat → Nat) :
    ∃ bytes, after = ⟨names, [(1, bytes)], after.highWater⟩ ∧ before.highWater ≤ after.highWater ∧
      restartFilesystem after (script bytes) = some (cold after.highWater bytes) ∧
      Concurrent.checkPost (repaired after.highWater left bytes.size) 64
        (.start (registered (cold after.highWater bytes))
          (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  obtain ⟨⟨data, captured, shape, positive⟩, high⟩ := repeated_prefix_crashes left count before after safe attempts
  obtain ⟨booted, accepted⟩ := reopens_captured_image after.highWater left data positive shape elapsed
  rw [← captured] at booted
  exact ⟨data, captured, high, booted, accepted⟩

open Record.MixedRepairWitness
  (beforeFailedSync interruptedImage restart_from_witness secondBoot secondImage
    second_interrupted_prefix)

set_option maxRecDepth 8192 in
private def witnessMasks : AdmittedMasks true [99,77,88] where
  closeSucceeds := false
  resizeMask := Record.MixedRepairWitness.resizeMask
  syncMask := Record.MixedRepairWitness.syncMask
  closeMask := Record.MixedRepairWitness.closeMask
  resized := withTail true [0,77]
  synchronized := withTail true [0]
  closed := contents true
  resize := by cbv
  sync := by cbv
  close := by cbv

private theorem first_interruption :
    InterruptedAttempt __TRY_REOPEN__ true
      ⟨names, [(1, withTail true [99,77,88])], 1⟩ interruptedImage := by
  obtain ⟨events, last, ran, _, crash⟩ := restart_from_witness.1
  refine ⟨[99,77,88], witnessMasks, beforeFailedSync, (fun _ _ => 0), events, last,
    names, Record.MixedRepairWitness.crashMask, by decide, rfl, ?_, ran, crash⟩
  exact boot_from_image 1 true [99,77,88] (by decide) witnessMasks (by decide)

set_option maxRecDepth 8192 in
private def secondMasks : AdmittedMasks true [0,77] where
  closeSucceeds := false
  resizeMask := Record.MixedRepairWitness.secondResizeMask
  syncMask := Record.MixedRepairWitness.syncMask
  closeMask := Record.MixedRepairWitness.closeMask
  resized := withTail true [0]
  synchronized := withTail true [0]
  closed := contents true
  resize := by cbv
  sync := by cbv
  close := by cbv

/-- Both attempts end between truncate and synchronize. The second attempt
starts from the first crash image, with a fresh error and descriptor. -/
theorem two_interrupted_attempts :
    InterruptedAttempts __TRY_REOPEN__ true 2
      ⟨names, [(1, withTail true [99,77,88])], 1⟩ secondImage := by
  obtain ⟨events, last, ran, _, crash⟩ := second_interrupted_prefix
  have second : InterruptedAttempt __TRY_REOPEN__ true interruptedImage secondImage :=
    ⟨[0,77], secondMasks, secondBoot, (fun _ _ => 0), events, last,
      names, Record.MixedRepairWitness.secondCrashMask, by decide, rfl,
      boot_from_image 3 true [0,77] (by decide) secondMasks (by decide), ran, crash⟩
  exact .next first_interruption (.next second .zero)

end Record.MixedRepairChains
