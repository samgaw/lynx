module
public import Record.NamedCloseInvariant

public section

open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol

namespace Record.NamedInterruptedRecovery
open NativeFile
open Record.NamedRepairCrash (JournalImage InterruptedRepair interrupted_preserves boot_from_image registerLog)
open Record.NamedCloseInvariant (typed_close_crash_preserves typed_repair_error_reports ioErrorCell openedWithError)
open Record.NamedJournalCrash (namedJournal)
open Record.NamedRustlerRepair (nameBytes boot bootWithFrame opened openScript arbitrary_repair_persists)

/-- A crash observes the actual consuming close reached after the typed
facade's extracted repair reports an error or rejects its record budget. -/
@[expose] def InterruptedClose (before after : FilesystemImage) : Prop :=
  ∃ (data : ByteArray) (choices rest : Term) (maximum : U32)
    (reply : core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError)
    (middle world : Environment) (residual : Result Unit)
    (chosen : Names) (masks : List (Nat × ByteArray)),
    before = ⟨namedJournal nameBytes, [(1, data)], before.highWater⟩ ∧
    (reply = .Ok none ∨ ∃ error, reply = .Err error) ∧
    Result.ReadyPrefix
      (repair_log ⟨before.highWater + 1⟩ (UScalar.cast .Usize maximum))
      (opened before.highWater data choices rest) (.ok (reply, ⟨before.highWater + 1⟩)) middle ∧
    Result.ReadyPrefix (NativeOwnedDrop.drop (⟨before.highWater + 1⟩ : NativeFile)) middle residual world ∧
    filesystemCrashImage chosen masks world = some after

private theorem close_interruption_preserves (values : List U16)
    (before after : FilesystemImage) (image : JournalImage values before)
    (attempt : InterruptedClose before after) :
    JournalImage values after ∧ after.highWater = before.highWater + 1 := by
  obtain ⟨positive, start, valid, bounded, initial⟩ := image
  obtain ⟨data, choices, rest, maximum, reply, middle, world, residual, names, masks,
    started, closing, repaired, closed, crash⟩ := attempt
  have equal : start = data := by
    simpa only [FilesystemImage.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] using
      initial.symm.trans started
  subst start
  obtain ⟨_, bytes, _, retained, fits, captured⟩ :=
    typed_close_crash_preserves before.highWater data choices rest values maximum positive bounded valid
      reply closing middle world residual repaired closed names masks after crash
  rw [captured]
  exact ⟨⟨by simp, bytes, retained, fits, rfl⟩, rfl⟩

/-- A restart after the compiled Rustler call has reported a repair error.
The host admits a fresh error capability above the captured high-water mark.
The descriptor open, close and typed conversion complete before power loss. -/
@[expose] def ReportedRepairFailure (before after : FilesystemImage) : Prop :=
  ∃ (data : ByteArray) (choices rest : Term) (maximum : U32) (middle closed world : Environment)
    (encode : NativeResourceArc shared_log.LogResource → Result Term) (names : Names)
    (masks : List (Nat × ByteArray)),
    before = ⟨namedJournal nameBytes, [(1, data)], before.highWater⟩ ∧
    Result.ReadyPrefix
      (repair_log ⟨before.highWater + 2⟩ (UScalar.cast .Usize maximum))
      (openedWithError (before.highWater + 1) (before.highWater + 1) data choices rest)
      (.ok (.Err (.os (before.highWater + 1)), ⟨before.highWater + 2⟩)) middle ∧
    Result.ReadyPrefix (NativeOwnedDrop.drop (⟨before.highWater + 2⟩ : NativeFile)) middle (.ok ()) closed ∧
    (Rustler.withNativeResult (__TRY_REOPEN__ maximum) encode)
      (bootWithFrame (before.highWater + 1) data choices rest [ioErrorCell (before.highWater + 1)]) =
      (.error (.error (.atom "journal_io")), world) ∧
    filesystemCrashImage names masks world = some after

private theorem reported_failure_preserves (values : List U16)
    (before after : FilesystemImage) (image : JournalImage values before)
    (attempt : ReportedRepairFailure before after) :
    JournalImage values after ∧ after.highWater = before.highWater + 2 := by
  obtain ⟨positive, start, valid, bounded, initial⟩ := image
  obtain ⟨data, choices, rest, maximum, middle, closed, world, encode, names, masks,
    started, repair, cleanup, reported, crash⟩ := attempt
  have equal : start = data := by
    simpa only [FilesystemImage.mk.injEq, List.cons.injEq, Prod.mk.injEq, true_and, and_true] using
      initial.symm.trans started
  subst start
  obtain ⟨final, ran, _, _, _, safe⟩ := typed_repair_error_reports (before.highWater + 1) (before.highWater + 1)
    data choices rest values maximum (by omega) (by omega) bounded valid middle closed repair cleanup encode
  have result := ran.apply
  rw [reported] at result
  have same : world = final := by
    simpa only [Result.error_apply] using congrArg Prod.snd result
  subst world
  obtain ⟨bytes, kept, fits, captured⟩ := safe names masks after crash
  rw [captured]
  exact ⟨⟨by simp, bytes, kept, fits, rfl⟩, rfl⟩

/-- Any number of restarts may be interrupted during repair or while its
typed caller is closing the file, or follow a reported I/O failure. Each new
attempt uses the prior disk image. The index counts allocations: one for
each descriptor, plus one for each reported OS error. -/
inductive InterruptedAttempts : Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : InterruptedAttempts 0 image image
  | next : (InterruptedRepair before middle ∨ InterruptedClose before middle) →
      InterruptedAttempts count middle after → InterruptedAttempts (count + 1) before after
  | reported : ReportedRepairFailure before middle → InterruptedAttempts count middle after →
      InterruptedAttempts (count + 2) before after

theorem interrupted_attempts_preserve (values : List U16) (before after : FilesystemImage)
    (count : Nat) (image : JournalImage values before)
    (attempts : InterruptedAttempts count before after) :
    JournalImage values after ∧ after.highWater = before.highWater + count := by
  induction attempts with
  | zero => exact ⟨image, by simp⟩
  | @next before middle count after step rest ih =>
    have still : JournalImage values middle ∧ middle.highWater = before.highWater + 1 := by
      rcases step with repair | closing
      · exact interrupted_preserves values before middle image repair
      · exact close_interruption_preserves values before middle image closing
    obtain ⟨last, fresh⟩ := ih still.1
    exact ⟨last, by have := still.2; omega⟩
  | @reported before middle count after step rest ih =>
    obtain ⟨kept, advance⟩ := reported_failure_preserves values before middle image step
    obtain ⟨last, fresh⟩ := ih kept
    exact ⟨last, by omega⟩

/-- Every actual successful typed retry after any admitted series of repair
or close interruptions and reported failures synchronizes exactly the
acknowledged records. -/
theorem typed_retry_after_interruptions (values : List U16) (before after : FilesystemImage) (count : Nat)
    (image : JournalImage values before) (attempts : InterruptedAttempts count before after) :
    ∃ bytes, after.highWater = before.highWater + count ∧
      ∀ choices rest : Term, (restartFilesystem after (openScript choices rest)).map registerLog =
        some (boot after.highWater bytes choices rest) ∧
        ∀ (maximum : U32) (owner : NativeResourceArc shared_log.LogResource) (world : Environment),
          Result.ReadyPrefix (__TRY_REOPEN__ maximum)
            (boot after.highWater bytes choices rest) (.ok (.Ok owner)) world →
          ∀ (chosen : Names) (masks : List (Nat × ByteArray)) (next : FilesystemImage),
            filesystemCrashImage chosen masks world = some next →
            next = ⟨namedJournal nameBytes, [(1, Record.CrashProperties.disk (Record.LogProperties.logBytes values))],
              before.highWater + count + 4⟩ := by
  obtain ⟨⟨positive, bytes, kept, bounded, captured⟩, advance⟩ :=
    interrupted_attempts_preserve values before after count image attempts
  refine ⟨bytes, advance, fun choices rest => ⟨?_, ?_⟩⟩
  · have restarted := boot_from_image after.highWater bytes choices rest positive bounded
    simpa only [← captured] using restarted
  · intro maximum owner world trace chosen masks next crash
    simpa only [advance] using
      arbitrary_repair_persists after.highWater bytes choices rest values maximum positive bounded
        kept owner world trace chosen masks next crash

end Record.NamedInterruptedRecovery
