module
public import Record.CompleteReopenAppend
public import Record.NamedSerialRecovery
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.ContinueSerialJournal
open NativeFile
open Record.ConcurrentRollback (initial reopenAndWrite all_prefixes_safe retained serialOrder recover_serial_log)
open Record.CompleteNamedRepair (completeBytes exactState capture_exact)
open Record.CompleteReopenAppend (reopenAppend resumeScript appendFinal appendState finalBytes)
open Record.ReopenedLogProperties (names finalEnvironment)
open Record.ReopenedRepairPrefix (CrashAttempts registered)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)

private theorem final_state (counter : Nat) (left committed : Bool) (last : Concurrent.Config Term)
    (accepted : appendFinal counter left committed last = true) :
    exactState counter (finalBytes left committed) last = true := by
  unfold appendFinal at accepted
  split at accepted
  · simp only [Bool.and_eq_true] at accepted
    have state := accepted.2
    unfold appendState at state
    dsimp only at state
    split at state
    · simp only [Bool.and_eq_true] at state
      tauto
    · contradiction
  · contradiction

/-- A new commit or rolled-back short write after any admitted restart
preserves the original callers' serial observation. The next crash must
retain the same named inode with the exact resulting journal bytes. -/
theorem survives_append_after_serial_recovery (committed : Bool) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term} {outcome : Outcome Term}
    (run : Concurrent.Run (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (finalEnvironment last) = some image) :
    ∃ left, outcome = .ok (serialOrder left).reply ∧
      ∀ count after, CrashAttempts (fun _ => __REOPEN__ 3#u32) count image after →
        ∃ boot, restartFilesystem after (resumeScript (completeBytes left) committed) = some boot ∧
          ∀ again nextEvents nextLast nextOutcome,
            Concurrent.Run (.start (registered boot) (reopenAppend __REOPEN__ __APPEND__) again) nextEvents nextLast →
            Concurrent.Terminal nextLast nextOutcome →
            appendFinal after.highWater left committed nextLast = true ∧
            ∀ chosen masks final, filesystemCrashImage chosen masks (finalEnvironment nextLast) = some final →
              final = ⟨names, [(1, finalBytes left committed)], final.highWater⟩ ∧ after.highWater ≤ final.highWater := by
  obtain ⟨left, reply, imageShape, _⟩ := recover_serial_log elapsed run terminal chosen masks image captured .nil
  have safe := all_prefixes_safe elapsed run
  simp only [retained, Bool.and_eq_true, decide_eq_true_eq] at safe
  have positive : 1 ≤ image.highWater := by simpa only [imageShape] using safe.1.1.1
  have exactImage : image = ⟨names, [(1, completeBytes left)], image.highWater⟩ := by
    have same : completeBytes left = disk (logBytes (serialOrder left).log) := by cases left <;> rfl
    rw [same, imageShape]
  refine ⟨left, reply, ?_⟩
  intro count after attempts
  obtain ⟨boot, ready, finishes⟩ :=
    Record.CompleteReopenAppend.append_after_repeated_reopen left committed count image after positive exactImage attempts
  refine ⟨boot, ready, ?_⟩
  intro again nextEvents nextLast nextOutcome execution done
  have accepted := finishes again nextEvents nextLast nextOutcome execution done
  exact ⟨accepted, fun chosen masks final crash =>
    capture_exact _ _ _ (final_state _ _ _ _ accepted) chosen masks final crash⟩

end Record.ContinueSerialJournal
