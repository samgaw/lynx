module
public import Record.ConcurrentRollback
public import Record.CompleteNamedRepair
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.NamedSerialRecovery
open NativeFile Record.ConcurrentRollback Record.CompleteNamedRepair
open Record.ReopenedLogProperties (names finalEnvironment)
open Record.ReopenedRepairPrefix (CrashAttempts reopenScript registered)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)

private theorem complete_encoding (leftFirst : Bool) :
    completeBytes leftFirst = disk (logBytes (serialOrder leftFirst).log) := by
  cases leftFirst <;> rfl

/-- The observed replies select the same serial log after every admitted
sequence of named reopens and crashes. The final successful host script
returns a resource for that exact named inode with a fresh VM pin. -/
theorem named_retry_after_serial_writes (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term} {outcome : Outcome Term}
    (run : Concurrent.Run (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (finalEnvironment last) = some image) :
    ∃ leftFirst, let result := serialOrder leftFirst
      let bytes := disk (logBytes result.log)
      outcome = .ok result.reply ∧
      ∀ count,
        CrashAttempts (fun _ => __REOPEN__ 3#u32) count image
          ⟨names, [(1, bytes)], image.highWater + count⟩ ∧
        ∀ after, CrashAttempts (fun _ => __REOPEN__ 3#u32) count image after →
          image.highWater ≤ after.highWater ∧
          after = ⟨names, [(1, bytes)], after.highWater⟩ ∧
          ∃ boot, restartFilesystem after (reopenScript bytes true) = some boot ∧
            ∀ elapsed events last outcome,
              Concurrent.Run (.start (registered boot) (finishComplete __REOPEN__) elapsed) events last →
              Concurrent.Terminal last outcome → completeReturn after.highWater bytes last = true := by
  obtain ⟨leftFirst, reply, named, _⟩ := recover_serial_log elapsed run terminal chosen masks image captured .nil
  have safe := all_prefixes_safe elapsed run
  simp only [retained, Bool.and_eq_true, decide_eq_true_eq] at safe
  have positive : 1 ≤ image.highWater := by simpa only [named] using safe.1.1.1
  have exactImage : image = ⟨names, [(1, completeBytes leftFirst)], image.highWater⟩ := by
    rw [complete_encoding, named]
  refine ⟨leftFirst, reply, fun count => ⟨?_, ?_⟩⟩
  · have witness := complete_attempts_witness image.highWater count leftFirst positive
    conv at witness =>
      enter [3]
      rw [← exactImage]
    simpa only [complete_encoding] using witness
  · intro after trace
    simpa only [complete_encoding] using retry_complete_log leftFirst count image after positive exactImage trace

end Record.NamedSerialRecovery
