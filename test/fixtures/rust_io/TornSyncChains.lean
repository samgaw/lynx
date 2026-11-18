module
public import Record.TornSyncRecovery
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.TornSyncChains
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (call contents environment openScript)
open Record.NamedJournalCrash (JournalBytes)
open Record.TornSyncFailure (boot withTail ioScript tail_forms)
open Record.TornSyncRecovery (names failed_sync_crash_reopens registered reopens_captured_image script cold repaired)

@[expose] def failedBootScript (counter tailLength : Nat) (syncTail closeTail : Fin 4)
    (closeSucceeds : Bool) : Term :=
  openScript true 0
    (ioScript tailLength (counter + 1) syncTail.val closeTail.val closeSucceeds) .nil

@[expose] def admitError (cold : Environment) : Environment :=
  let error := cold.nativeRefCounter + 1
  { registered cold with
    nativeRefCounter := error
    nativeHeap := cold.nativeHeap ++ [(error, NativeIoError.typeName, .atom "live")] }

set_option maxRecDepth 8192 in
/-- The modeled error capability is admitted after restart. The only old
filesystem objects are the persistent name and inode in the crash image. -/
theorem boot_from_image (counter : Nat) (left : Bool) (tail : List UInt8)
    (short : tail.length < 4) (syncTail closeTail : Fin 4)
    (closeSucceeds : Bool) (positive : 1 ≤ counter) :
    (restartFilesystem ⟨names, [(1, withTail left tail)], counter⟩
      (failedBootScript counter tail.length syncTail closeTail closeSucceeds)).map admitError =
      some (boot counter left tail syncTail.val closeTail.val closeSucceeds) := by
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    cases left <;> cbv

@[expose] def JournalImage (left : Bool) (image : FilesystemImage) : Prop :=
  ∃ data, image = ⟨names, [(1, data)], image.highWater⟩ ∧ JournalBytes (contents left) data ∧
    1 ≤ image.highWater

/-- An actual typed sync failure and subsequent reset from a short-tail image.
The admitted I/O error is fresh on each boot. -/
abbrev Reopen := U32 → NativeM (core.result.Result
  (NativeResourceArc shared_log.LogResource) Rustler.DecoderError)

@[expose] def FailedAttempt (reopen : Reopen) (left : Bool) (before after : FilesystemImage) : Prop :=
  ∃ (tail : List UInt8) (syncTail closeTail : Fin 4) (closeSucceeds : Bool) (started : Environment)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (outcome : Outcome Term) (chosen : Names) (masks : List (Nat × ByteArray)),
    tail.length < 4 ∧ syncTail.val ≤ tail.length ∧ closeTail.val ≤ syncTail.val ∧
    before = ⟨names, [(1, withTail left tail)], before.highWater⟩ ∧
    (restartFilesystem before
      (failedBootScript before.highWater tail.length syncTail closeTail closeSucceeds)).map admitError =
      some started ∧
    Concurrent.Run (.start started
      (call reopen 3#u32) elapsed) events last ∧
    Concurrent.Terminal last outcome ∧ filesystemCrashImage chosen masks (environment last) = some after

inductive FailedAttempts (reopen : Reopen) (left : Bool) : Nat → FilesystemImage → FilesystemImage → Prop where
  | zero : FailedAttempts reopen left 0 image image
  | next : FailedAttempt reopen left before middle → FailedAttempts reopen left n middle after →
      FailedAttempts reopen left (n + 1) before after

private theorem failed_attempt_keeps_image (left : Bool) (before after : FilesystemImage)
    (safe : JournalImage left before) (attempt : FailedAttempt __TRY_REOPEN__ left before after) :
    JournalImage left after ∧ after.highWater = before.highWater + 2 := by
  obtain ⟨_, _, _, positive⟩ := safe
  obtain ⟨tail, syncTail, closeTail, closeSucceeds, started, elapsed, events, last, outcome, chosen,
    masks, short, syncBound, closeBound, prior, restarted, run, terminal, crash⟩ := attempt
  have rebuilt := boot_from_image before.highWater left tail short syncTail closeTail
    closeSucceeds positive
  have equal : started = boot before.highWater left tail syncTail.val closeTail.val closeSucceeds := by
    rw [prior] at restarted
    simpa only [rebuilt, Option.some.injEq] using restarted.symm
  rw [equal] at run
  obtain ⟨data, captured, shape, _⟩ := failed_sync_crash_reopens before.highWater left tail short
    syncTail closeTail syncBound closeBound closeSucceeds positive elapsed (fun _ _ => 0)
    events last outcome run terminal chosen masks after crash
  have high : after.highWater = before.highWater + 2 := congrArg FilesystemImage.highWater captured
  refine ⟨⟨data, ?_, shape, by omega⟩, high⟩
  simpa only [high] using captured

/-- A finite chain of modeled Rustler sync failures and crashes preserves both
acknowledged records and advances capability freshness at every attempt. -/
theorem repeated_failed_sync (left : Bool) (count : Nat) (before after : FilesystemImage)
    (safe : JournalImage left before) (attempts : FailedAttempts __TRY_REOPEN__ left count before after) :
    JournalImage left after ∧ after.highWater = before.highWater + 2 * count := by
  induction attempts with
  | zero => simpa
  | @next before middle n after attempt rest ih =>
    have first := failed_attempt_keeps_image left before middle safe attempt
    have later := ih first.1
    exact ⟨later.1, by omega⟩

set_option maxRecDepth 8192 in
/-- Repeated accepted crash images leave no old owners. The next successful
restart returns an inode-linked writable resource for the same journal. -/
theorem reopens_after_failed_attempts (left : Bool) (count : Nat) (before after : FilesystemImage)
    (safe : JournalImage left before)
    (attempts : FailedAttempts __TRY_REOPEN__ left count before after)
    (elapsed : PID → Nat → Nat) :
    ∃ data, after = ⟨names, [(1, data)], before.highWater + 2 * count⟩ ∧
      restartFilesystem after (script data) = some (cold after.highWater data) ∧
      Concurrent.checkPost (repaired after.highWater left data.size) 64
        (.start (registered (cold after.highWater data)) (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  obtain ⟨⟨data, captured, shape, positive⟩, high⟩ := repeated_failed_sync left count before after safe attempts
  have reopened := reopens_captured_image after.highWater left data positive shape elapsed
  refine ⟨data, ?_, ?_, reopened.2⟩
  · simpa only [high] using captured
  · have restarted := reopened.1
    rw [← captured] at restarted
    exact restarted

end Record.TornSyncChains
