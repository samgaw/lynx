module
public import Record.NamedConcurrentWriterCrash
public import Record.SharedReadProperties

public section
open Aeneas Aeneas.Std Lynx io_protocol NativeFile

namespace Record.NamedConcurrentWriterRecovery
open Record.NamedConcurrentRepairWriter (initial names writers acknowledged)
open Record.ConcurrentRepairWriterInvariant (snapshot)
open Record.CrashProperties (recoveryScript scanning)
open Record.SharedReadProperties (boot reopened openingScript named_log_prefix_restart)

/-- Every admitted crash of the two-writer run can restart the named inode.
The actual opener and parser recover the old record and every observed append
under the admitted successful read script, even with an unacknowledged suffix. -/
theorem recover_acknowledgements (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start initial (writers locked_repair_and_append) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (rest : Term)
    (crash : filesystemCrashImage chosen masks (snapshot last) = some image) :
    ∃ (values : List U16) (bytes : ByteArray) (capacity : values.length ≤ 262144),
      13#u16 ∈ values ∧
      (acknowledged 19 (snapshot last) = true → 19#u16 ∈ values) ∧
      (acknowledged 23 (snapshot last) = true → 23#u16 ∈ values) ∧
      let script := recoveryScript bytes rest
      restartFilesystem image (openingScript script) = some (boot image.highWater bytes script) ∧
      io_core.open_readonly (toStr "journal") (boot image.highWater bytes script) =
        (.ok (.Ok ⟨image.highWater + 1⟩), reopened image.highWater names ⟨bytes, bytes, 0, script⟩) ∧
      recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
        (reopened image.highWater names ⟨bytes, bytes, 0, script⟩) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
          reopened image.highWater names (scanning bytes rest (4 * values.length))) := by
  obtain ⟨values, bytes, captured, positive, fits, capacity, encoded, oldRecord, firstRecord, secondRecord⟩ :=
    Record.NamedConcurrentWriterCrash.prefix_crash elapsed events last run chosen masks image crash
  refine ⟨values, bytes, capacity, oldRecord, firstRecord, secondRecord, ?_⟩
  have highWater : 1 ≤ (snapshot last).nativeRefCounter := by
    simpa only [captured] using positive
  dsimp only
  rw [captured]
  exact named_log_prefix_restart _ values bytes rest highWater fits encoded capacity

end Record.NamedConcurrentWriterRecovery
