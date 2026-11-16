module
public import GuardedRecovery.Extraction.Funs
public import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.ReadTrace

@[expose] def one (value : U8) : Slice U8 := .from [value] (by scalar_tac)
@[expose] def word (low high : U8) : U16 :=
  core.num.U16.from_le_bytes (Array.make 2#usize [low,high])

/-- Admitted host transitions for every branch of the actual two-byte parser.
The equations refer to executable file polls, not assumed first-party contracts. -/
inductive Reads (file : NativeFile) : Environment →
    core.result.Result (Option U16) NativeIoError → Environment → Prop where
  | firstError {before after : Environment} (error : NativeIoError)
      (read : NativeFile.pollRead file (one 0#u8) before =
        some (.ok (.Err error,file,one 0#u8),after)) : Reads file before (.Err error) after
  | firstEof {before after : Environment}
      (read : NativeFile.pollRead file (one 0#u8) before =
        some (.ok (.Ok 0#usize,file,one 0#u8),after)) : Reads file before (.Ok none) after
  | secondError {before middle after : Environment} (low : U8) (error : NativeIoError)
      (first : NativeFile.pollRead file (one 0#u8) before =
        some (.ok (.Ok 1#usize,file,one low),middle))
      (second : NativeFile.pollRead file (one 0#u8) middle =
        some (.ok (.Err error,file,one 0#u8),after)) : Reads file before (.Err error) after
  | secondEof {before middle after : Environment} (low : U8)
      (first : NativeFile.pollRead file (one 0#u8) before =
        some (.ok (.Ok 1#usize,file,one low),middle))
      (second : NativeFile.pollRead file (one 0#u8) middle =
        some (.ok (.Ok 0#usize,file,one 0#u8),after)) : Reads file before (.Ok none) after
  | complete {before middle after : Environment} (low high : U8)
      (first : NativeFile.pollRead file (one 0#u8) before =
        some (.ok (.Ok 1#usize,file,one low),middle))
      (second : NativeFile.pollRead file (one 0#u8) middle =
        some (.ok (.Ok 1#usize,file,one high),after)) :
      Reads file before (.Ok (some (word low high))) after

private theorem read_next {file : NativeFile} {buffer updated : Slice U8}
    {before middle after : Environment} {reply : core.result.Result Usize NativeIoError}
    {next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α}
    {value : α}
    (poll : NativeFile.pollRead file buffer before = some (.ok (reply,file,updated),middle))
    (tail : Result.ReadyPrefix (next (reply,file,updated)) middle (.ok value) after) :
    Result.ReadyPrefix (io_core.read_once file buffer >>= next) before (.ok value) after := by
  simp only [io_core.read_once,monadLift_self,NativeFile.read,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ poll
  simpa only [Result.ok_bind] using tail

/-- Every admitted branch executes the actual extracted parser, including its
mutable-array reconstruction and fixed-width little-endian conversion. -/
theorem Reads.ready {file : NativeFile} {before after : Environment}
    {reply : core.result.Result (Option U16) NativeIoError} (trace : Reads file before reply after) :
    Result.ReadyPrefix (read_word file) before (.ok (reply,file)) after := by
  cases trace <;>
    simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
      Array.to_slice_mut,Array.to_slice,Array.make_val]
  case firstError error read =>
    apply read_next read
    simpa [NativeM.ok] using Result.ReadyPrefix.refl (.ok ((core.result.Result.Err error : core.result.Result (Option U16) NativeIoError),file)) _
  case firstEof read =>
    apply read_next read
    simpa [NativeM.ok] using Result.ReadyPrefix.refl (.ok ((core.result.Result.Ok none : core.result.Result (Option U16) NativeIoError),file)) _
  case secondError low error first second =>
    apply read_next first
    simp only [UScalar.ofNatCore_val_eq]
    apply read_next second
    simpa [NativeM.ok] using Result.ReadyPrefix.refl (.ok ((core.result.Result.Err error : core.result.Result (Option U16) NativeIoError),file)) _
  case secondEof low first second =>
    apply read_next first
    simp only [UScalar.ofNatCore_val_eq]
    apply read_next second
    simpa [NativeM.ok] using Result.ReadyPrefix.refl (.ok ((core.result.Result.Ok none : core.result.Result (Option U16) NativeIoError),file)) _
  case complete low high first second =>
    apply read_next first
    simp only [UScalar.ofNatCore_val_eq]
    apply read_next second
    simpa [NativeM.ok,Array.from_slice,Array.index_usize,one,
      NativeM.monadLift_eq,NativeM.fromRust,word,Result.ok_bind] using
      Result.ReadyPrefix.refl (.ok ((core.result.Result.Ok (some (word low high)) : core.result.Result (Option U16) NativeIoError),file)) _

@[expose] def recoverGuard :
    core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)) →
      NativeGuard NativeFile
  | .Ok guard => guard
  | .Err error => NativePoisonError.into_inner error

@[expose] def finish (guard : NativeGuard NativeFile)
    (reply : core.result.Result (Option U16) NativeIoError) :
    NativeM (core.result.Result (Option U16) U8) := do
  match reply with
  | .Ok value =>
    NativeGuard.release guard
    NativeM.ok (.Ok value)
  | .Err error =>
    NativeIoError.dispose error
    NativeGuard.release guard
    NativeM.ok (.Err 1#u8)

@[expose] def critical (guard : NativeGuard NativeFile) (offset : U64) :
    NativeM (core.result.Result (Option U16) U8) := do
  let (reply,file) ← io_core.seek_from guard.value (core.io.seek.SeekFrom.Start offset)
  match reply with
  | .Err error => finish {guard with value := file} (.Err error)
  | .Ok _ =>
    let (reply,file) ← read_word file
    finish {guard with value := file} reply

/-- This normalized critical section is definitionally linked to both branches
of the actual extracted lock/poison handling and owned destructor calls. -/
theorem locked_contract (mutex : NativeMutex NativeFile) (offset : U64) :
    locked_word mutex offset = (do
      let acquired ← NativeMutex.lock mutex
      critical (recoverGuard acquired) offset) := by
  simp only [locked_word,monadLift_self,NativeM.lift,NativeM.ok,Result.ok_bind,
    NativeGuard.deref_mut,NativeOwnedDrop.drop]
  apply congrArg (fun next => NativeMutex.lock mutex >>= next)
  funext acquired
  cases acquired <;> simp only [recoverGuard,critical,finish,NativeM.ok]
  all_goals
    apply congrArg (fun next => io_core.seek_from _ _ >>= next)
    funext result
    obtain ⟨reply,file⟩ := result
    cases reply <;> rfl

@[expose] def disposed (error : NativeIoError) (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)}

/-- Successful release and admitted OS-error destruction are separate checks.
Error disposal uses the post-read environment, retaining every earlier mutation. -/
inductive Finished (guard : NativeGuard NativeFile) :
    core.result.Result (Option U16) NativeIoError → Environment →
    core.result.Result (Option U16) U8 → Environment → Prop where
  | success {before after : Environment} (value : Option U16)
      (release : NativeGuard.pollRelease guard before = some (.ok (),after)) :
      Finished guard (.Ok value) before (.Ok value) after
  | error {before after : Environment} (error : NativeIoError)
      (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ before.nativeRefCounter)
      (stored : before.nativeHeap.filter (fun cell => cell.1 == error.identity) =
        [(error.identity,NativeIoError.typeName,.atom "live")])
      (release : NativeGuard.pollRelease guard (disposed error before) = some (.ok (),after)) :
      Finished guard (.Err error) before (.Err 1#u8) after

private theorem release_next {guard : NativeGuard NativeFile} {before middle after : Environment}
    {next : NativeM α} {value : α}
    (release : NativeGuard.pollRelease guard before = some (.ok (),middle))
    (tail : Result.ReadyPrefix next middle (.ok value) after) :
    Result.ReadyPrefix (do NativeGuard.release guard; next) before (.ok value) after := by
  simp only [NativeGuard.release,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ release
  simpa only [Result.ok_bind] using tail

theorem Finished.ready {guard : NativeGuard NativeFile} {before after : Environment}
    {reply : core.result.Result (Option U16) NativeIoError}
    {value : core.result.Result (Option U16) U8} (trace : Finished guard reply before value after) :
    Result.ReadyPrefix (finish guard reply) before (.ok value) after := by
  cases trace with
  | success value release =>
    apply release_next release
    exact .refl _ _
  | error error nonzero bounded stored release =>
    simp only [finish,NativeIoError.dispose,Result.consumeNativeCapability,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ (.ok ()) _ (disposed error before) _ _
    · simp [nonzero,not_lt.mpr bounded,stored,disposed]
    · simp only [Result.ok_bind,Result.ofExcept]
      apply release_next release
      exact .refl _ _

/-- Every successful seek follows the actual parser trace; failed seeks bypass
reads and consume the admitted error before releasing the same held guard. -/
inductive Critical (guard : NativeGuard NativeFile) (offset : U64) : Environment →
    core.result.Result (Option U16) U8 → Environment → Prop where
  | seekError {before sought after : Environment} (error : NativeIoError)
      (seek : NativeFile.pollSeek guard.value (.start offset) before =
        some (.ok (.Err error,guard.value),sought))
      (finish : Finished guard (.Err error) sought (.Err 1#u8) after) :
      Critical guard offset before (.Err 1#u8) after
  | read {before sought readAfter after : Environment} (position : U64)
      (reply : core.result.Result (Option U16) NativeIoError)
      (value : core.result.Result (Option U16) U8)
      (seek : NativeFile.pollSeek guard.value (.start offset) before =
        some (.ok (.Ok position,guard.value),sought))
      (reads : Reads guard.value sought reply readAfter)
      (finish : Finished guard reply readAfter value after) :
      Critical guard offset before value after

theorem Critical.ready {guard : NativeGuard NativeFile} {offset : U64}
    {before after : Environment} {value : core.result.Result (Option U16) U8}
    (trace : Critical guard offset before value after) :
    Result.ReadyPrefix (critical guard offset) before (.ok value) after := by
  cases trace with
  | seekError error seek finishTrace =>
    simp only [critical,io_core.seek_from,GuardedRecovery.Extraction.FileModel.seek,monadLift_self,NativeFile.seek,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ seek
    simpa only [Result.ok_bind] using finishTrace.ready
  | read position reply value seek reads finishTrace =>
    simp only [critical,io_core.seek_from,GuardedRecovery.Extraction.FileModel.seek,monadLift_self,NativeFile.seek,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ seek
    simp only [Result.ok_bind]
    have first := reads.ready.bind (fun (reply,file) => finish {guard with value := file} reply)
    apply first.trans
    simpa only [Result.ok_bind] using finishTrace.ready

/-- Arbitrary admitted lock, seek/read and destructor transitions execute the
actual Rust critical section, including poisoned-lock recovery. -/
theorem locked_ready (mutex : NativeMutex NativeFile) (offset : U64)
    (before acquired after : Environment)
    (reply : core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)))
    (value : core.result.Result (Option U16) U8)
    (lock : NativeMutex.pollLock mutex before = some (.ok reply,acquired))
    (trace : Critical (recoverGuard reply) offset acquired value after) :
    Result.ReadyPrefix (locked_word mutex offset) before (.ok value) after := by
  rw [locked_contract]
  simp only [NativeMutex.lock,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ lock
  simpa only [Result.ok_bind] using trace.ready

theorem locked_every_run (mutex : NativeMutex NativeFile) (offset : U64)
    (before acquired after : Environment)
    (reply : core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)))
    (value : core.result.Result (Option U16) U8)
    (lock : NativeMutex.pollLock mutex before = some (.ok reply,acquired))
    (trace : Critical (recoverGuard reply) offset acquired value after)
    (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start before (locked_word mutex offset) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) : outcome = .ok value :=
  (locked_ready mutex offset before acquired after reply value lock trace).returns elapsed run terminal

inductive Scenario where
  | complete | firstEof | secondEof | firstError | secondError | seekError

@[expose] def data : Scenario → ByteArray
  | .firstEof => ⟨#[]⟩
  | .secondEof => ⟨#[7]⟩
  | _ => ⟨#[7,8]⟩
@[expose] def mask (scenario : Scenario) : ByteArray :=
  ⟨(data scenario).data.map (fun _ => 0)⟩
@[expose] def action (scenario : Scenario) (operation : String) (success : Bool)
    (value : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom (if success then "ok" else "error"),
    .integer value,.bitstring (mask scenario) 0]) rest
@[expose] def reads (scenario : Scenario) : Term :=
  match scenario with
  | .firstEof => action scenario "read" true 0 .nil
  | .firstError => action scenario "read" false 3 .nil
  | .secondEof => action scenario "read" true 1 (action scenario "read" true 0 .nil)
  | .secondError => action scenario "read" true 1 (action scenario "read" false 3 .nil)
  | _ => action scenario "read" true 1 (action scenario "read" true 1 .nil)
@[expose] def script (scenario : Scenario) : Term :=
  if let .seekError := scenario then action scenario "seek" false 3 .nil else
  action scenario "seek" true 0 (reads scenario)
@[expose] def hasError : Scenario → Bool
  | .firstError | .secondError | .seekError => true
  | _ => false
@[expose] def position : Scenario → Nat
  | .complete => 2
  | .secondEof | .secondError => 1
  | _ => 0
@[expose] def output : Scenario → core.result.Result (Option U16) U8
  | .complete => .Ok (some (word 7#u8 8#u8))
  | .firstEof | .secondEof => .Ok none
  | _ => .Err 1#u8
@[expose] def mutex : NativeMutex NativeFile := ⟨1⟩
@[expose] def file : NativeFile := ⟨2⟩
@[expose] def guard (counter : Nat) : NativeGuard NativeFile :=
  ⟨mutex,counter+1,({} : Environment).currentPid,file⟩
@[expose] def initial (counter : Nat) (poisoned : Bool) (scenario : Scenario) : Environment := {
  nativeRefCounter := counter
  nativeHeap := [
    (1,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
      .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file]),
    (2,NativeFile.typeName,NativeFile.encode ⟨data scenario,data scenario,0,script scenario⟩)] ++
    (if hasError scenario then [(3,NativeIoError.typeName,.atom "live")] else []) }
@[expose] def acquired (counter : Nat) (poisoned : Bool) (scenario : Scenario) : Environment := {
  (initial counter poisoned scenario) with
  nativeRefCounter := counter+1
  nativeHeap := (initial counter poisoned scenario).nativeHeap.map fun cell =>
    if cell.1 == 1 then (1,NativeMutex.typeName NativeFile,
      NativeMutex.lockedContents ({} : Environment).currentPid (counter+1) poisoned file)
    else cell }
@[expose] def finished (counter : Nat) (poisoned : Bool) (scenario : Scenario) : Environment := {
  nativeRefCounter := counter+1
  nativeHeap := [
    (1,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
      .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file]),
    (2,NativeFile.typeName,NativeFile.encode ⟨data scenario,data scenario,position scenario,.nil⟩)] }

@[expose] def held (counter : Nat) (poisoned : Bool) (scenario : Scenario)
    (position : Nat) (rest : Term) (errorLive : Bool) : Environment := {
  nativeRefCounter := counter+1
  nativeHeap := [
    (1,NativeMutex.typeName NativeFile,
      NativeMutex.lockedContents ({} : Environment).currentPid (counter+1) poisoned file),
    (2,NativeFile.typeName,NativeFile.encode ⟨data scenario,data scenario,position,rest⟩)] ++
    (if errorLive then [(3,NativeIoError.typeName,.atom "live")] else []) }
@[expose] def nativeOutput : Scenario → core.result.Result (Option U16) NativeIoError
  | .complete => .Ok (some (word 7#u8 8#u8))
  | .firstEof | .secondEof => .Ok none
  | _ => .Err (.os 3)

open scoped Lynx.NativeArithmetic

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem admitted_reads (counter : Nat) (poisoned : Bool) (scenario : Scenario)
    (positive : 3 ≤ counter) (reading : scenario ≠ .seekError) :
    Reads file (held counter poisoned scenario 0 (reads scenario) (hasError scenario))
      (nativeOutput scenario)
      (held counter poisoned scenario (position scenario) .nil (hasError scenario)) := by
  cases scenario with
  | complete =>
    apply Reads.complete (middle := held counter poisoned .complete 1
      (action .complete "read" true 1 .nil) false) 7#u8 8#u8 <;> cases poisoned <;> cbv
  | firstEof => apply Reads.firstEof; cases poisoned <;> cbv
  | secondEof =>
    apply Reads.secondEof (middle := held counter poisoned .secondEof 1
      (action .secondEof "read" true 0 .nil) false) 7#u8 <;> cases poisoned <;> cbv
  | firstError => apply Reads.firstError ⟨3⟩; cases poisoned <;> cbv
  | secondError =>
    apply Reads.secondError (middle := held counter poisoned .secondError 1
      (action .secondError "read" false 3 .nil) true) 7#u8 ⟨3⟩ <;> cases poisoned <;> cbv
  | seekError => exact False.elim (reading rfl)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem admitted_finish (counter : Nat) (poisoned : Bool) (scenario : Scenario)
    (positive : 3 ≤ counter) :
    Finished (guard counter) (nativeOutput scenario)
      (held counter poisoned scenario (position scenario) .nil (hasError scenario))
      (output scenario) (finished counter poisoned scenario) := by
  cases scenario with
  | complete => apply Finished.success _; cases poisoned <;> cbv
  | firstEof => apply Finished.success _; cases poisoned <;> cbv
  | secondEof => apply Finished.success _; cases poisoned <;> cbv
  | firstError =>
    apply Finished.error ⟨3⟩
    · decide
    · change 3 ≤ counter + 1
      omega
    · cases poisoned <;> cbv
    · cases poisoned <;> cbv
  | secondError =>
    apply Finished.error ⟨3⟩
    · decide
    · change 3 ≤ counter + 1
      omega
    · cases poisoned <;> cbv
    · cases poisoned <;> cbv
  | seekError =>
    apply Finished.error ⟨3⟩
    · decide
    · change 3 ≤ counter + 1
      omega
    · cases poisoned <;> cbv
    · cases poisoned <;> cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem admitted_critical (counter : Nat) (poisoned : Bool) (scenario : Scenario)
    (positive : 3 ≤ counter) :
    Critical (guard counter) 0#u64 (acquired counter poisoned scenario)
      (output scenario) (finished counter poisoned scenario) := by
  by_cases failure : scenario = .seekError
  · subst scenario
    apply Critical.seekError (sought := held counter poisoned .seekError 0 .nil true) ⟨3⟩
    · cases poisoned <;> cbv
    · exact admitted_finish counter poisoned .seekError positive
  · apply Critical.read
      (sought := held counter poisoned scenario 0 (reads scenario) (hasError scenario))
      (readAfter := held counter poisoned scenario (position scenario) .nil (hasError scenario))
      0#u64 (nativeOutput scenario) (output scenario)
    · cases scenario <;> try contradiction
      all_goals cases poisoned <;> cbv
    · exact admitted_reads counter poisoned scenario positive failure
    · exact admitted_finish counter poisoned scenario positive

@[expose] def lockReply (counter : Nat) (poisoned : Bool) :
    core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)) :=
  if poisoned then .Err ⟨guard counter⟩ else .Ok (guard counter)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- All six concrete host scenarios admit both poison states at any fresh counter.
The result includes exact file-offset/script state and error/guard cleanup. -/
theorem admitted_locked (counter : Nat) (poisoned : Bool) (scenario : Scenario)
    (positive : 3 ≤ counter) :
    Result.ReadyPrefix (locked_word mutex 0#u64) (initial counter poisoned scenario)
      (.ok (output scenario)) (finished counter poisoned scenario) := by
  have recovered : recoverGuard (lockReply counter poisoned) = guard counter := by
    cases poisoned <;> rfl
  apply locked_ready mutex 0#u64 _ (acquired counter poisoned scenario) _
    (lockReply counter poisoned) (output scenario)
  · cases scenario <;> cases poisoned <;> cbv
  · simpa only [recovered] using admitted_critical counter poisoned scenario positive

@[expose] def withoutError (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != 3)}

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- An unadmitted destructor exhausts verification at the actual error cleanup.
It neither certifies error return nor silently releases the still-held guard. -/
theorem missing_error_exhausts (counter : Nat) (poisoned : Bool) (scenario : Scenario)
    (positive : 3 ≤ counter) (error : hasError scenario = true) :
    Concurrent.checkPost (fun config => match config with
      | .start env (.error .exhausted) _ =>
        (Concurrent.nativeEnvironment env).identical (Concurrent.nativeEnvironment
          (held counter poisoned scenario (position scenario) .nil false))
      | _ => false) 128
      (.start (withoutError (initial counter poisoned scenario)) (locked_word mutex 0#u64)) = true := by
  cases scenario <;> try contradiction
  all_goals cases poisoned <;> cbv

end GuardedRecovery.ReadTrace
