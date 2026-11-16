module
public import GuardedRecovery.RecoveryCompleteness
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.RecoveryRun

private theorem no_panic_local {computation : NativeM α}
    (safe : NativeM.NoPanic computation) (env : Environment) :
    Result.NativeInvariant (fun _ => True) computation env := by
  intro residual after trace
  have remaining := safe.ready_prefix trace
  refine ⟨trivial,?_⟩
  cases remaining <;> trivial

private theorem from_rust_local (computation : RustM α) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (NativeM.fromRust computation) env := by
  unfold NativeM.fromRust
  split
  · exact .ok _ _ _ trivial
  · exact .error _ _ _ trivial
  · exact .error _ _ _ trivial

private theorem read_once_local (file : NativeFile) (buffer : Slice U8) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (io_core.read_once file buffer) env := by
  simp only [io_core.read_once,monadLift_self,NativeFile.read]
  apply Result.NativeInvariant.wait _ _ _ trivial
  intro reply after _
  cases reply with
  | ok value => exact .ok _ _ _ trivial
  | error exception => exact .error _ _ _ trivial

private theorem read_word_local (file : NativeFile) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (read_word file) env := by
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  apply (read_once_local _ _ env).bind
  intro result middle _
  obtain ⟨reply,file,buffer⟩ := result
  dsimp only
  cases reply with
  | Err error => exact .ok _ _ _ trivial
  | Ok count =>
    dsimp only
    split
    · exact .ok _ _ _ trivial
    · apply (read_once_local _ _ middle).bind
      intro result after _
      obtain ⟨reply,file,buffer⟩ := result
      dsimp only
      cases reply with
      | Err error => exact .ok _ _ _ trivial
      | Ok count =>
        dsimp only
        split
        · exact .ok _ _ _ trivial
        · simp only [NativeM.monadLift_eq]
          apply (from_rust_local _ after).bind
          intro low afterLow _
          apply (from_rust_local _ afterLow).bind
          intro high afterHigh _
          exact .ok _ _ _ trivial

private theorem seek_local (file : NativeFile) (offset : U64) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (io_core.seek_from file (.Start offset)) env := by
  simp only [io_core.seek_from,GuardedRecovery.Extraction.FileModel.seek,monadLift_self,NativeFile.seek]
  apply Result.NativeInvariant.wait _ _ _ trivial
  intro reply after _
  cases reply with
  | ok value => exact .ok _ _ _ trivial
  | error exception => exact .error _ _ _ trivial

private theorem finish_local (guard : NativeGuard NativeFile)
    (reply : core.result.Result (Option U16) NativeIoError) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (GuardedRecovery.ReadTrace.finish guard reply) env := by
  cases reply with
  | Ok value =>
    unfold GuardedRecovery.ReadTrace.finish
    apply (no_panic_local (NativeM.NoPanic.guard_release guard) env).bind
    intro _ after _
    exact .ok _ _ _ trivial
  | Err error =>
    unfold GuardedRecovery.ReadTrace.finish
    apply (no_panic_local (NativeM.NoPanic.io_error_dispose error) env).bind
    intro _ disposed _
    apply (no_panic_local (NativeM.NoPanic.guard_release guard) disposed).bind
    intro _ after _
    exact .ok _ _ _ trivial

private theorem critical_local (guard : NativeGuard NativeFile) (offset : U64) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (GuardedRecovery.ReadTrace.critical guard offset) env := by
  unfold GuardedRecovery.ReadTrace.critical
  apply (seek_local _ _ env).bind
  intro result sought _
  obtain ⟨reply,file⟩ := result
  dsimp only
  cases reply with
  | Err error => exact finish_local _ _ sought
  | Ok position =>
    apply (read_word_local _ sought).bind
    intro result readAfter _
    exact finish_local _ _ readAfter

private theorem locked_local (mutex : NativeMutex NativeFile) (offset : U64) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (locked_word mutex offset) env := by
  rw [GuardedRecovery.ReadTrace.locked_contract]
  apply (no_panic_local (NativeM.NoPanic.mutex_lock mutex) env).bind
  intro acquired after _
  exact critical_local _ _ after

private theorem cell_local (tag : String) (identity : Nat) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (NativeM.readCell tag identity) env := by
  unfold NativeM.readCell
  apply Result.NativeInvariant.nativeGet
  split
  · split
    · exact .ok _ _ _ trivial
    · exact .error _ _ _ trivial
  · exact .error _ _ _ trivial

private theorem remove_local (tag : String) (identity : Nat) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (NativeM.removeCell tag identity) env := by
  unfold NativeM.removeCell
  apply Result.NativeInvariant.wait _ _ _ trivial
  intro reply after _
  cases reply with
  | ok value => exact .ok _ _ _ trivial
  | error exception => exact .error _ _ _ trivial

private theorem close_local (file : NativeFile) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (NativeFile.close file) env := by
  unfold NativeFile.close
  apply Result.NativeInvariant.wait _ _ _ trivial
  intro reply after _
  cases reply with
  | ok value => exact .ok _ _ _ trivial
  | error exception => exact .error _ _ _ trivial

private theorem cleanup_local (mutex : NativeMutex NativeFile) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (NativeMutex.disposeFile mutex) env := by
  unfold NativeMutex.disposeFile
  apply (cell_local _ _ env).bind
  intro contents before _
  cases contents with
  | tuple fields =>
    dsimp only
    split
    · split
      · split
        · rename_i file _
          apply (close_local file before).bind
          intro _ closed _
          apply (remove_local _ _ closed).bind
          intro _ removed _
          exact .ok _ _ _ trivial
        · exact .error _ _ _ trivial
      · exact .error _ _ _ trivial
    · exact .error _ _ _ trivial
  | _ => exact .error _ _ _ trivial

private theorem body_local (mutex : NativeMutex NativeFile) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (GuardedRecovery.RecoveryTrace.body mutex) env := by
  unfold GuardedRecovery.RecoveryTrace.body
  apply (locked_local _ _ env).bind
  intro first middle _
  cases first with
  | Err error =>
    unfold GuardedRecovery.RecoveryTrace.finish
    apply (cleanup_local mutex middle).bind
    intro _ after _
    exact .ok _ _ _ trivial
  | Ok first =>
    apply (locked_local _ _ middle).bind
    intro second readAfter _
    unfold GuardedRecovery.RecoveryTrace.finish
    apply (cleanup_local mutex readAfter).bind
    intro _ after _
    exact .ok _ _ _ trivial

private theorem allocation_local (file : NativeFile) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (NativeMutex.new file) env := by
  unfold NativeMutex.new
  apply Result.NativeInvariant.bind
  · unfold NativeM.allocate
    apply Result.NativeInvariant.wait _ _ _ trivial
    intro reply after _
    cases reply with
    | ok value => exact .ok _ _ _ trivial
    | error exception => exact .error _ _ _ trivial
  · intro identity after _
    exact .ok _ _ _ trivial

private theorem open_local (path : Str) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (io_core.open_readonly path) env := by
  simp only [io_core.open_readonly,monadLift_self,NativeFile.openReadOnly]
  apply Result.NativeInvariant.wait _ _ _ trivial
  intro reply after _
  cases reply with
  | ok value => exact .ok _ _ _ trivial
  | error exception => exact .error _ _ _ trivial

/-- All prefixes of the actual extracted Rust recovery remain native/local,
including exceptional, blocked and exhausted paths. No IO success is assumed. -/
theorem reopen_local (path : Str) (env : Environment) :
    Result.NativeInvariant (fun _ => True) (reopen_words path) env := by
  rw [GuardedRecovery.RecoveryTrace.reopen_contract]
  apply (open_local path env).bind
  intro opened middle _
  cases opened with
  | Ok file =>
    apply (allocation_local file middle).bind
    intro mutex allocated _
    exact body_local mutex allocated
  | Err error =>
    apply (no_panic_local (NativeM.NoPanic.io_error_dispose error) middle).bind
    intro _ after _
    exact .ok _ _ _ trivial

/-- Every successful terminal scheduler run of the actual Rust recovery comes
from an admitted recovery trace and retains its exact final environment. -/
theorem reopen_run_complete (path : Str) (before : Environment) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start before (reopen_words path) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok value)) :
    ∃ after, GuardedRecovery.RecoveryTrace.Reopens path before value after ∧
      last = .start after (.ok value) elapsed := by
  obtain ⟨after,prefixTrace,equal⟩ := (reopen_local path before).run_returns elapsed run terminal
  exact ⟨after,GuardedRecovery.RecoveryCompleteness.reopen_complete prefixTrace,equal⟩

end GuardedRecovery.RecoveryRun
