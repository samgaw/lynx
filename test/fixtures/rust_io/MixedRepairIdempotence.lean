module
public import Record.MixedRepairChains
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx

namespace Record.MixedRepairIdempotence
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (journalName call contents environment)
open Record.NamedJournalCrash (JournalBytes captured_journal inodeIds names_equal)
open Record.TornSyncChains (JournalImage Reopen)
open Record.TornSyncRecovery (names script cold registered reopens_captured_image repairState repaired)
open Record.MixedRepairChains (InterruptedAttempts repeated_prefix_crashes)

private theorem capture_completed (counter : Nat) (left : Bool) (eof : Nat)
    (last : Concurrent.Config Term) (success : repaired counter left eof last = true)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (environment last) = some image) :
    image = ⟨names, [(1, contents left)], counter + 6⟩ := by
  unfold repaired at success
  split at success
  · simp only [Bool.and_eq_true, beq_iff_eq] at success
    have exactState := success.2
    unfold repairState at exactState
    split at exactState
    · rename_i handle file table opened found snapshot
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at exactState
      have visible : file.visible = contents left := ByteArray.ext (by tauto)
      have durable : file.durable = contents left := ByteArray.ext (by tauto)
      have named : namespaceSnapshot (environment last) = some ⟨names,names,[],table.script⟩ := by
        rw [snapshot]
        have live : table.names = names := names_equal _ _ (by tauto)
        have stable : table.committed = names := names_equal _ _ (by tauto)
        have settled : table.pending = [] := by tauto
        cases table
        simp_all
      have ids : inodeIds (environment last) = [1] := by tauto
      have high : (environment last).nativeRefCounter = counter + 6 := by tauto
      obtain ⟨mask, bytes, allowed, imageEq⟩ :=
        captured_journal journalName _ file table.script named ids found chosen masks image captured
      rw [visible, durable] at allowed
      rw [imageEq, persist_same _ _ _ allowed, high]
      rfl
    · contradiction
  · contradiction

/-- A fresh boot of a captured journal under the successful recovery script,
followed by a terminal return and a subsequent admitted filesystem crash. -/
@[expose] def CompletedRecovery (reopen : Reopen) (before after : FilesystemImage) : Prop :=
  ∃ (bytes : ByteArray) (boot : Environment) (elapsed : PID → Nat → Nat)
    (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (outcome : Outcome Term) (chosen : Names) (masks : List (Nat × ByteArray)),
    before = ⟨names, [(1, bytes)], before.highWater⟩ ∧
    restartFilesystem before (script bytes) = some boot ∧
    Concurrent.Run (.start (registered boot) (call reopen 3#u32) elapsed) events last ∧
    Concurrent.Terminal last outcome ∧
    filesystemCrashImage chosen masks (environment last) = some after

inductive CompletedRecoveries (reopen : Reopen) :
    Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : CompletedRecoveries reopen 0 image image
  | next : CompletedRecovery reopen before middle →
      CompletedRecoveries reopen count middle after →
      CompletedRecoveries reopen (count + 1) before after

private theorem one_completed_recovery (left : Bool) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (attempt : CompletedRecovery __TRY_REOPEN__ before after) :
    after = ⟨names, [(1, contents left)], before.highWater + 6⟩ := by
  obtain ⟨stored, captured, shape, positive⟩ := safe
  obtain ⟨bytes, boot, elapsed, events, last, outcome, chosen, masks, contentsEq, restart,
    ran, terminal, nextCrash⟩ := attempt
  have byteEq : bytes = stored := by
    have same := congrArg FilesystemImage.inodes (contentsEq.symm.trans captured)
    simpa using same
  subst stored
  have check := reopens_captured_image before.highWater left bytes positive shape elapsed
  have bootEq : boot = cold before.highWater bytes := by
    rw [contentsEq, check.1] at restart
    exact (Option.some.inj restart).symm
  rw [bootEq] at ran
  exact capture_completed before.highWater left bytes.size last
    (Concurrent.checkPost_sound check.2 ran terminal) chosen masks after nextCrash

/-- Each completed repair leaves the same exact bytes regardless of the crash
mask. Every reboot still allocates a fresh writable resource. -/
theorem idempotent_completed_recovery (left : Bool) (count : Nat) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (attempts : CompletedRecoveries __TRY_REOPEN__ count before after) :
    JournalImage left after ∧ after.highWater = before.highWater + 6 * count ∧
      (0 < count → after.inodes = [(1, contents left)]) := by
  induction attempts with
  | zero => exact ⟨safe, by simp, by omega⟩
  | @next before middle count after attempt rest ih =>
    have image := one_completed_recovery left before middle safe attempt
    have stored : JournalBytes (contents left) (contents left) :=
      ⟨⟨le_rfl, fun _ _ => rfl⟩, by omega⟩
    have safeMiddle : JournalImage left middle := by
      rw [image]
      exact ⟨contents left, rfl, stored, by simp⟩
    obtain ⟨safeAfter, high, ending⟩ := ih safeMiddle
    refine ⟨safeAfter, ?_, ?_⟩
    · rw [high, image]
      simp only [FilesystemImage.highWater]
      omega
    · intro _
      by_cases remaining : 0 < count
      · exact ending remaining
      · have zero : count = 0 := by omega
        subst count
        cases rest
        rw [image]

/-- A sequence of interrupted repairs can be followed by any positive
number of completed repairs and crashes. The complete image is then
idempotent while the native allocator stays fresh across every boot. -/
theorem mixed_then_completed (left : Bool) (interruptions completions : Nat)
    (before middle after : FilesystemImage) (safe : JournalImage left before)
    (interrupted : InterruptedAttempts __TRY_REOPEN__ left interruptions before middle)
    (completed : CompletedRecoveries __TRY_REOPEN__ completions middle after)
    (positive : 0 < completions) :
    after = ⟨names, [(1, contents left)], middle.highWater + 6 * completions⟩ ∧
      before.highWater + 6 * completions ≤ after.highWater := by
  obtain ⟨safeMiddle, advance⟩ := repeated_prefix_crashes left interruptions before middle safe interrupted
  obtain ⟨⟨bytes, shape, _, _⟩, high, finish⟩ :=
    idempotent_completed_recovery left completions middle after safeMiddle completed
  have same : bytes = contents left := by
    have inodes := congrArg FilesystemImage.inodes shape
    rw [finish positive] at inodes
    simpa using inodes.symm
  refine ⟨?_, by rw [high]; omega⟩
  rw [← high, ← same]
  exact shape

end Record.MixedRepairIdempotence
