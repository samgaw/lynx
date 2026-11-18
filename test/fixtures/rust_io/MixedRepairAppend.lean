module
public import Record.MixedRepairChains
public import Record.TypedRestartAppend

public section

open Lynx

namespace Record.MixedRepairAppend
open NativeFile
open Record.FallibleReopen (environment)
open Record.TornSyncFailure (withTail)
open Record.TornSyncRecovery (names script image_shape registered)
open Record.TornSyncChains (JournalImage)
open Record.MixedRepairWitness (secondImage)
open Record.MixedRepairChains (InterruptedAttempts repeated_prefix_crashes two_interrupted_attempts)
open Record.TypedRestartAppend
  (accepted appendScript boot finalBytes reopenAppend typed_reopen_append crash_after_typed_append)

/-- After any number of admitted mixed-mask interruptions, the recovered
journal can be continued by the two compiled NIFs. A later power loss retains
the exact committed or rolled-back records of that continuation. -/
theorem appends_after_mixed_interruptions (left committed : Bool) (count : Nat)
    (before after : FilesystemImage) (safe : JournalImage left before)
    (attempts : InterruptedAttempts __TRY_REOPEN__ left count before after) :
    ∃ bytes restarted,
      restartFilesystem after (script bytes (appendScript committed)) = some restarted ∧
      ∀ elapsed events last outcome,
        Concurrent.Run
          (.start (registered restarted) (reopenAppend __TRY_REOPEN__ __APPEND__) elapsed)
          events last → Concurrent.Terminal last outcome →
        accepted after.highWater left committed last = true ∧
        ∀ chosen masks image,
          filesystemCrashImage chosen masks (environment last) = some image →
          image = ⟨names, [(1, finalBytes left committed)], after.highWater + 8⟩ := by
  obtain ⟨⟨data, stored, shape, positive⟩, _⟩ :=
    repeated_prefix_crashes left count before after safe attempts
  obtain ⟨tail, short, rfl⟩ := image_shape left data shape
  refine ⟨withTail left tail, boot after.highWater (withTail left tail) committed, ?_, ?_⟩
  · have ready := (typed_reopen_append after.highWater left committed tail positive short (fun _ _ => 0)).1
    rw [← stored] at ready
    exact ready
  · intro elapsed events last outcome ran terminal
    have checked := (typed_reopen_append after.highWater left committed tail positive short elapsed).2
    exact ⟨Concurrent.checkPost_sound checked ran terminal,
      crash_after_typed_append after.highWater left committed tail positive short elapsed
        events last outcome ran terminal⟩

@[expose] def commitBoot : Environment := registered (boot 5 (withTail true [0]) true)

set_option maxRecDepth 8192 in
/-- The commit law starts from the durable image of the second interruption. -/
theorem boot_after_two_interruptions :
    InterruptedAttempts __TRY_REOPEN__ true 2
      ⟨names, [(1, withTail true [99,77,88])], 1⟩ secondImage ∧
    (restartFilesystem secondImage (script (withTail true [0]) (appendScript true))).map registered =
      some commitBoot := by
  exact ⟨two_interrupted_attempts, by cbv⟩

theorem committed_outcome (last : Concurrent.Config Term)
    (safe : accepted 5 true true last = true) : last.outcome = .ok Term.true := by
  unfold accepted at safe
  split at safe
  · rename_i reply returned
    simp [Bool.and_eq_true] at safe
    rw [safe.1] at returned
    exact returned
  · contradiction

end Record.MixedRepairAppend
