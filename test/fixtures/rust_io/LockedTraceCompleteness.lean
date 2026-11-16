module
public import GuardedRecovery.ReadCompleteness
public import GuardedRecovery.RecoveryTrace
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.LockedCompleteness
open GuardedRecovery.ReadTrace GuardedRecovery.ReadCompleteness

private theorem release_returns {guard : NativeGuard NativeFile} {before after : Environment}
    (trace : Result.ReadyPrefix (NativeGuard.release guard) before (.ok ()) after) :
    NativeGuard.pollRelease guard before = some (.ok (),after) := by
  simp only [NativeGuard.release] at trace
  obtain ⟨response,middle,poll,rest⟩ := trace.wait_returns
  cases response with
  | error exception => cases rest
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    exact poll

private theorem seek_returns {file returnedFile : NativeFile} {offset : U64}
    {before after : Environment} {reply : core.result.Result U64 NativeIoError}
    (trace : Result.ReadyPrefix (io_core.seek_from file (.Start offset)) before
      (.ok (reply,returnedFile)) after) :
    returnedFile = file ∧ NativeFile.pollSeek file (.start offset) before =
      some (.ok (reply,returnedFile),after) := by
  simp only [io_core.seek_from,GuardedRecovery.Extraction.FileModel.seek,monadLift_self,NativeFile.seek] at trace
  obtain ⟨response,middle,poll,rest⟩ := trace.wait_returns
  cases response with
  | error exception => cases rest
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    refine ⟨?_,poll⟩
    unfold NativeFile.pollSeek at poll
    split at poll
    · simp at poll
    · split at poll
      · simp at poll
      · split at poll
        · simp at poll
        · simp only [Option.some.injEq,Prod.mk.injEq,Except.ok.injEq] at poll
          exact poll.1.2.symm

/-- Completed disposal derives its unique live OS-error admission and exact removal. -/
theorem dispose_returns {error : NativeIoError} {before after : Environment}
    (trace : Result.ReadyPrefix (NativeIoError.dispose error) before (.ok ()) after) :
    error.identity ≠ 0 ∧ error.identity ≤ before.nativeRefCounter ∧
      before.nativeHeap.filter (fun cell => cell.1 == error.identity) =
        [(error.identity,NativeIoError.typeName,.atom "live")] ∧ after = disposed error before := by
  simp only [NativeIoError.dispose,Result.consumeNativeCapability] at trace
  obtain ⟨response,middle,poll,rest⟩ := trace.wait_returns
  cases response with
  | error exception => cases rest
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    simp only [Option.some.injEq] at poll
    split at poll
    · simp at poll
    · rename_i valid
      simp only [not_or,not_lt] at valid
      split at poll
      · rename_i identity storedType matching
        split at poll
        · rename_i sameType
          have member : (identity,storedType,.atom "live") ∈
              before.nativeHeap.filter (fun cell => cell.1 == error.identity) := by
            rw [matching]
            simp
          have sameIdentity : identity = error.identity := by
            simpa using (List.mem_filter.mp member).2
          have typeEqual : storedType = NativeIoError.typeName := by simpa using sameType
          exact ⟨valid.1,valid.2,by simpa [sameIdentity,typeEqual] using matching,
            (Prod.mk.inj poll).2.symm⟩
        · simp at poll
      · simp at poll

theorem finish_complete {guard : NativeGuard NativeFile} {before after : Environment}
    {reply : core.result.Result (Option U16) NativeIoError}
    {value : core.result.Result (Option U16) U8}
    (trace : Result.ReadyPrefix (finish guard reply) before (.ok value) after) :
    Finished guard reply before value after := by
  cases reply with
  | Ok input =>
    simp only [finish] at trace
    obtain ⟨returned,middle,released,rest⟩ := trace.bind_returns
    cases returned
    have poll := release_returns released
    simp only [NativeM.ok] at rest
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    exact .success input poll
  | Err error =>
    simp only [finish] at trace
    obtain ⟨returned,middle,removed,rest⟩ := trace.bind_returns
    cases returned
    obtain ⟨nonzero,bounded,stored,rfl⟩ := dispose_returns removed
    obtain ⟨returned,middle,released,rest⟩ := rest.bind_returns
    cases returned
    have poll := release_returns released
    simp only [NativeM.ok] at rest
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    exact .error error nonzero bounded stored poll

theorem critical_complete {guard : NativeGuard NativeFile} {offset : U64}
    {before after : Environment} {value : core.result.Result (Option U16) U8}
    (trace : Result.ReadyPrefix (critical guard offset) before (.ok value) after) :
    Critical guard offset before value after := by
  simp only [critical] at trace
  obtain ⟨⟨seekReply,file⟩,sought,seekTrace,rest⟩ := trace.bind_returns
  obtain ⟨rfl,poll⟩ := seek_returns seekTrace
  cases seekReply with
  | Err error =>
    have finished := finish_complete rest
    cases finished with
    | error _ nonzero bounded stored release =>
      exact .seekError error poll (.error error nonzero bounded stored release)
  | Ok position =>
    obtain ⟨⟨reply,file⟩,readAfter,readTrace,rest⟩ := rest.bind_returns
    obtain ⟨rfl,reads⟩ := reads_complete readTrace
    exact .read position reply value poll reads (finish_complete rest)

/-- Completed extracted critical sections must acquire an actual guard and
follow the admitted seek, read, error-disposal and release transitions. -/
theorem locked_complete {mutex : NativeMutex NativeFile} {offset : U64}
    {before after : Environment} {value : core.result.Result (Option U16) U8}
    (trace : Result.ReadyPrefix (locked_word mutex offset) before (.ok value) after) :
    ∃ reply acquired, NativeMutex.pollLock mutex before = some (.ok reply,acquired) ∧
      Critical (recoverGuard reply) offset acquired value after := by
  rw [locked_contract] at trace
  obtain ⟨acquired,middle,head,rest⟩ := trace.bind_returns
  have criticalTrace := critical_complete rest
  simp only [NativeMutex.lock] at head
  obtain ⟨response,polled,poll,tail⟩ := head.wait_returns
  cases response with
  | error exception => cases tail
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := tail.ok_returns
    exact ⟨returned,polled,poll,criticalTrace⟩

/-- The complete relation retains both unpoisoned and poisoned acquisition,
all parser outcomes and exact cleanup states of the actual Rust caller. -/
theorem locked_iff (mutex : NativeMutex NativeFile) (offset : U64)
    (before after : Environment) (value : core.result.Result (Option U16) U8) :
    Result.ReadyPrefix (locked_word mutex offset) before (.ok value) after ↔
      GuardedRecovery.RecoveryTrace.Locked mutex offset before value after := by
  constructor
  · intro trace
    obtain ⟨reply,acquired,poll,criticalTrace⟩ := locked_complete trace
    exact .acquired acquired reply poll criticalTrace
  · intro trace
    exact trace.ready

end GuardedRecovery.LockedCompleteness
