module
public import FileResource.RecordErrors
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.RecordCleanup
open NativeFile FileResource.RecordRecovery FileResource.RecordErrors
open FileResource.Recovery (one)

/-- This is the actual remaining destructor and error return, not a replacement
for the Rust reader or a hypothesis about its result. -/
@[expose] def cleanup (generation error : Nat) : NativeM (core.result.Result (Option U16) NativeIoError) := do
  NativeOwnedDrop.drop (⟨generation + 1⟩ : NativeFile)
  NativeM.ok (.Err ⟨error⟩)

variable (a b c d : U8) (generation : Nat) (validGeneration : 1 ≤ generation)
include validGeneration

/-- An actual failing read reaches the actual destructor at its retained cursor. -/
theorem before_close (position error : Nat) (inside : position < 4) (closeError : Option Nat) :
    Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (RecordErrors.boot a b c d generation (reads error (closing closeError) position))
      (cleanup generation error) (scan a b c d generation position (closing closeError)) := by
  interval_cases position
  all_goals simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (RecordErrors.open_poll a b c d generation validGeneration _)
  all_goals simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,effects_core.read_file_record,effects_core.read_file_word,
    NativeM.lift,monadLift_self,Array.to_slice_mut,Array.to_slice,Array.make_val,
    bind_assoc,effects_core.read_file_once,NativeFile.read,Result.wait_bind,reads,successRead,failedRead]
  · apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (error_poll a b c d generation validGeneration 0 error (by decide +kernel) _)
    simp only [NativeM.ok,Result.ok_bind,cleanup]
    exact .refl _ _
  all_goals apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (success_poll a b c d generation validGeneration 0 (by decide +kernel) _)
  all_goals simp only [NativeM.ok]
  · apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (error_poll a b c d generation validGeneration 1 error (by decide +kernel) _)
    simp only [NativeM.ok,Result.ok_bind,cleanup]
    exact .refl _ _
  all_goals apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (success_poll a b c d generation validGeneration 1 (by decide +kernel) _)
  all_goals simp [Array.from_slice,one,Array.index_usize,NativeM.fromRust,Result.ok_bind]
  · apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (error_poll a b c d generation validGeneration 2 error (by decide +kernel) _)
    simp only [NativeM.ok,Result.ok_bind,cleanup]
    exact .refl _ _
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (success_poll a b c d generation validGeneration 2 (by decide +kernel) _)
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (error_poll a b c d generation validGeneration 3 error (by decide +kernel) _)
  simp only [NativeM.ok,Result.ok_bind,cleanup]
  exact .refl _ _

/-- Closing, including an ignored close error, is a real final ownership step. -/
theorem after_close (position error : Nat) (inside : position < 4) (closeError : Option Nat) :
    Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (RecordErrors.boot a b c d generation (reads error (closing closeError) position))
      (.ok (.Err ⟨error⟩)) (scan a b c d generation position .nil true) := by
  apply (before_close a b c d generation validGeneration position error inside closeError).trans
  simp only [cleanup,NativeOwnedDrop.drop,close,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _
    (RecordErrors.close_poll a b c d generation validGeneration position (by omega) closeError)
  simp only [Result.ok_bind,NativeM.ok]
  exact .refl _ _

/-- Both selected crash states retain a prefix of the actual Rust computation. -/
theorem cleanup_prefix (position error : Nat) (inside : position < 4)
    (closeError : Option Nat) (closed : Bool) :
    ∃ residual, Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (RecordErrors.boot a b c d generation (reads error (closing closeError) position))
      residual (cleanupState a b c d generation position closeError closed) := by
  cases closed
  · exact ⟨cleanup generation error,before_close a b c d generation validGeneration position error inside closeError⟩
  · exact ⟨.ok (.Err ⟨error⟩),after_close a b c d generation validGeneration position error inside closeError⟩

omit validGeneration in
/-- An admitted crash before or after failed-read destruction composes with
restart, further mixed recovery attempts and actual final checked recovery. -/
theorem cleanup_retry (value : U16) (generation : Nat) (valid : 1 ≤ generation)
    (position error : Nat) (inside : position < 4) (closeError : Option Nat) (closed : Bool)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
    (accepted : filesystemCrashImage chosen masks
      (cleanupState (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position closeError closed) = some image)
    (trace : RecordErrors.Attempts value image.highWater last) :
    (∃ residual, Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (RecordErrors.boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation (reads error (closing closeError) position))
      residual (cleanupState (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position closeError closed)) ∧
    restartFilesystem image openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last 4 .nil true) := by
  have admitted : filesystemCrashImage chosen masks
      (RecordRetry.phaseEnv (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation .finished) = some image := by
    rw [cleanup_crash_eq _ _ _ _ generation valid position closeError closed] at accepted
    exact accepted
  have same := RecordRetry.phase_crash _ _ _ _ generation valid .finished chosen masks image admitted
  have fresh : 1 ≤ image.highWater := by rw [same]; change 1 ≤ generation + 1; omega
  refine ⟨cleanup_prefix _ _ _ _ generation valid position error inside closeError closed,?_,
    (RecordErrors.finite_attempts value image.highWater last trace fresh).2.2⟩
  rw [same]
  exact RecordRecovery.restart_image _ _ _ _ (generation + 1) (by omega)

omit validGeneration in
/-- Each cleanup side has an actual execution prefix and a concrete admitted
crash, excluding a vacuous retry relation. -/
theorem cleanup_witness (value : U16) (generation : Nat) (valid : 1 ≤ generation)
    (position error : Nat) (inside : position < 4) (closeError : Option Nat) (closed : Bool) :
    (∃ residual, Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (RecordErrors.boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation (reads error (closing closeError) position))
      residual (cleanupState (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position closeError closed)) ∧
    filesystemCrashImage Publish.names [(1,⟨#[0,0,0,0]⟩)]
      (cleanupState (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position closeError closed) =
      some ⟨Publish.names,[(1,Record.content value)],generation + 1⟩ ∧
    RecordErrors.Attempts value generation (generation + 1) := by
  have admitted : filesystemCrashImage Publish.names [(1,⟨#[0,0,0,0]⟩)]
      (cleanupState (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position closeError closed) =
      some ⟨Publish.names,[(1,Record.content value)],generation + 1⟩ := by
    rw [cleanup_crash_eq _ _ _ _ generation valid position closeError closed,content_layout]
    exact RecordRetry.phase_witness _ _ _ _ generation valid .finished
  exact ⟨cleanup_prefix _ _ _ _ generation valid position error inside closeError closed,
    admitted,.failed generation position error inside closeError closed Publish.names [(1,⟨#[0,0,0,0]⟩)]
      ⟨Publish.names,[(1,Record.content value)],generation + 1⟩ _ admitted (.done _)⟩

omit validGeneration in
/-- An actual successful NIF transaction precedes the admitted initial crash,
finite interrupted recovery trace and final recovery of the acknowledged value. -/
theorem transaction_attempts (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (finalGeneration : Nat)
    (accepted : filesystemCrashImage chosen masks (Record.done env value) = some image)
    (trace : RecordErrors.Attempts value image.highWater finalGeneration) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
        (Creation.initial env Record.before.script Publish.opening) =
      (.ok Term.true,Record.done env value) ∧
    restartFilesystem image openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration 4 .nil true) := by
  exact ⟨Record.create_write_commit env value registered,
    RecordErrors.committed_attempts env value chosen masks image finalGeneration accepted trace⟩

end FileResource.RecordCleanup
