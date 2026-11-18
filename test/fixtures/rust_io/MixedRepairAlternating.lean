module
public import Record.MixedRepairIdempotence

public section

open Lynx

namespace Record.MixedRepairAlternating
open NativeFile
open Record.FallibleReopen (contents)
open Record.TornSyncFailure (withTail)
open Record.TornSyncRecovery (names image_shape)
open Record.TornSyncChains (JournalImage Reopen)
open Record.MixedRepairRecovery (packed_size)
open Record.MixedRepairChains (InterruptedAttempt interrupted_preserves journalLength)
open Record.MixedRepairIdempotence (CompletedRecovery completed_preserves)

/-- An arbitrary sequence of actual repair crashes. Attempts may be
interrupted or run to completion before crashing, in any order. -/
inductive RecoveryCrashes (reopen : Reopen) (left : Bool) :
    Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : RecoveryCrashes reopen left 0 image image
  | interrupted : InterruptedAttempt reopen left before middle →
      RecoveryCrashes reopen left count middle after →
      RecoveryCrashes reopen left count before after
  | completed : CompletedRecovery reopen before middle →
      RecoveryCrashes reopen left count middle after →
      RecoveryCrashes reopen left (count + 1) before after

private theorem at_least_prefix (left : Bool) (image : FilesystemImage)
    (safe : JournalImage left image) : 8 ≤ journalLength image := by
  obtain ⟨bytes, imageEq, shape, _⟩ := safe
  obtain ⟨tail, _, rfl⟩ := image_shape left bytes shape
  rw [imageEq]
  change 8 ≤ (withTail left tail).size
  rw [packed_size]
  omega

private theorem exact_complete (left : Bool) (image : FilesystemImage)
    (safe : JournalImage left image) (bounded : journalLength image ≤ 8) :
    image.inodes = [(1, contents left)] := by
  obtain ⟨bytes, imageEq, shape, _⟩ := safe
  obtain ⟨tail, _, rfl⟩ := image_shape left bytes shape
  have small : (withTail left tail).size ≤ 8 := by
    rw [imageEq] at bounded
    exact bounded
  rw [packed_size] at small
  have empty : tail = [] := List.eq_nil_of_length_eq_zero (by omega)
  rw [imageEq, empty]
  cases left <;> rfl

/-- After every crash the acknowledged prefix is retained. Once an
attempt completes, subsequent failed or interrupted attempts cannot
increase the durable length or reintroduce the discarded tail. The
counter never decreases across interrupted attempts and accounts for
exactly six allocations per completed repair. -/
theorem alternating_repairs (left : Bool) (completed : Nat) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (attempts : RecoveryCrashes __TRY_REOPEN__ left completed before after) :
    JournalImage left after ∧ journalLength after ≤ journalLength before ∧
      before.highWater + 6 * completed ≤ after.highWater ∧
      (0 < completed → after.inodes = [(1, contents left)]) := by
  induction attempts with
  | zero => exact ⟨safe, le_rfl, by simp, by omega⟩
  | @interrupted before middle count after attempt rest ih =>
    obtain ⟨safeMiddle, advance, shrunk⟩ := interrupted_preserves left before middle safe attempt
    obtain ⟨safeAfter, shorter, high, exactAfter⟩ := ih safeMiddle
    exact ⟨safeAfter, shorter.trans shrunk, by omega, exactAfter⟩
  | @completed before middle count after attempt rest ih =>
    have image := completed_preserves left before middle safe attempt
    have safeMiddle : JournalImage left middle := by
      rw [image]
      exact ⟨contents left, rfl, ⟨⟨le_rfl, fun _ _ => rfl⟩, by omega⟩, by simp⟩
    obtain ⟨safeAfter, shorter, high, _⟩ := ih safeMiddle
    have completeLength : journalLength middle = 8 := by
      rw [image]
      cases left <;> rfl
    have allows : journalLength after ≤ 8 := shorter.trans_eq completeLength
    have advance : middle.highWater = before.highWater + 6 := by rw [image]
    exact ⟨safeAfter, allows.trans (at_least_prefix left before safe), by omega,
      fun _ => exact_complete left after safeAfter allows⟩

end Record.MixedRepairAlternating
