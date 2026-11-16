module
public import GuardedRecovery.ReadTrace
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.RecoveryTrace
open GuardedRecovery.ReadTrace (Critical recoverGuard)

abbrev Reply := core.result.Result (Option U16 × Option U16) U8

/-- Acquisition and critical-section evidence for the actual Rust caller. -/
inductive Locked (mutex : NativeMutex NativeFile) (offset : U64)
    (before : Environment) (value : core.result.Result (Option U16) U8) (after : Environment) : Prop where
  | acquired (acquired : Environment)
      (reply : core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)))
      (lock : NativeMutex.pollLock mutex before = some (.ok reply,acquired))
      (critical : Critical (recoverGuard reply) offset acquired value after) :
      Locked mutex offset before value after

theorem Locked.ready {mutex : NativeMutex NativeFile} {offset : U64}
    {before after : Environment} {value : core.result.Result (Option U16) U8}
    (trace : Locked mutex offset before value after) :
    Result.ReadyPrefix (locked_word mutex offset) before (.ok value) after := by
  cases trace with
  | acquired acquired reply lock critical =>
    exact GuardedRecovery.ReadTrace.locked_ready mutex offset before acquired after reply value lock critical

/-- Owning cleanup checks the actual close poll and retains the mutex until
that close completes, before removing only its own typed cell. -/
inductive Cleanup (mutex : NativeMutex NativeFile) : Environment → Environment → Prop where
  | close (file : NativeFile) (poisoned : Bool) (before closed : Environment)
      (stored : before.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
        [(mutex.id,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file])])
      (poll : NativeFile.pollClose file before = some (.ok (),closed))
      (retained : closed.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
        [(mutex.id,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode file])]) :
      Cleanup mutex before {closed with nativeHeap := closed.nativeHeap.filter (fun cell => cell.1 != mutex.id)}

theorem Cleanup.ready {mutex : NativeMutex NativeFile} {before after : Environment}
    (trace : Cleanup mutex before after) :
    Result.ReadyPrefix (NativeMutex.disposeFile mutex) before (.ok ()) after := by
  cases trace with
  | close file poisoned before closed stored poll retained =>
    exact NativeMutex.disposeFile_prefix mutex file poisoned before closed stored poll retained

@[expose] def pairReply (first : Option U16) : core.result.Result (Option U16) U8 → Reply
  | .Ok second => .Ok (first,second)
  | .Err error => .Err error
@[expose] def finish (mutex : NativeMutex NativeFile) (value : Reply) : NativeM Reply := do
  NativeMutex.disposeFile mutex
  NativeM.ok value
@[expose] def body (mutex : NativeMutex NativeFile) : NativeM Reply := do
  let first ← locked_word mutex 0#u64
  match first with
  | .Ok first =>
    let second ← locked_word mutex 2#u64
    finish mutex (pairReply first second)
  | .Err error => finish mutex (.Err error)

/-- No first-party contract is assumed: the normalized body is proved equal to
all branches of the actual extracted open, lock, read and owned-drop sequence. -/
theorem reopen_contract (path : Str) :
    reopen_words path = (do
      let opened ← io_core.open_readonly path
      match opened with
      | .Ok file =>
        let mutex ← NativeMutex.new file
        body mutex
      | .Err error =>
        NativeIoError.dispose error
        NativeM.ok (.Err 3#u8)) := by
  simp only [reopen_words,monadLift_self,NativeM.ok,NativeOwnedDrop.drop]
  apply congrArg (fun next => io_core.open_readonly path >>= next)
  funext opened
  cases opened with
  | Err error => rfl
  | Ok file =>
    apply congrArg (fun next => NativeMutex.new file >>= next)
    funext mutex
    unfold body
    apply congrArg (fun next => locked_word mutex 0#u64 >>= next)
    funext first
    cases first with
    | Err error => rfl
    | Ok first =>
      apply congrArg (fun next => locked_word mutex 2#u64 >>= next)
      funext second
      cases second <;> rfl

inductive Body (mutex : NativeMutex NativeFile) : Environment → Reply → Environment → Prop where
  | firstError {before readAfter after : Environment} (error : U8)
      (first : Locked mutex 0#u64 before (.Err error) readAfter)
      (cleanup : Cleanup mutex readAfter after) : Body mutex before (.Err error) after
  | second {before middle readAfter after : Environment} (first : Option U16)
      (second : core.result.Result (Option U16) U8)
      (readFirst : Locked mutex 0#u64 before (.Ok first) middle)
      (readSecond : Locked mutex 2#u64 middle second readAfter)
      (cleanup : Cleanup mutex readAfter after) : Body mutex before (pairReply first second) after

private theorem finish_ready {mutex : NativeMutex NativeFile} {before after : Environment}
    (value : Reply) (cleanup : Cleanup mutex before after) :
    Result.ReadyPrefix (finish mutex value) before (.ok value) after := by
  have ran := cleanup.ready.bind (fun _ => NativeM.ok value)
  simpa only [Result.ok_bind,finish,NativeM.ok] using ran

theorem Body.ready {mutex : NativeMutex NativeFile} {before after : Environment} {value : Reply}
    (trace : Body mutex before value after) :
    Result.ReadyPrefix (body mutex) before (.ok value) after := by
  cases trace with
  | firstError error first cleanup =>
    unfold body
    apply (first.ready.bind _).trans
    simpa only [Result.ok_bind] using finish_ready (.Err error) cleanup
  | second first second readFirst readSecond cleanup =>
    unfold body
    apply (readFirst.ready.bind _).trans
    simp only [Result.ok_bind]
    apply (readSecond.ready.bind _).trans
    simpa only [Result.ok_bind] using finish_ready (pairReply first second) cleanup

@[expose] def initialized (file : NativeFile) (env : Environment) : Environment := {env with
  nativeRefCounter := env.nativeRefCounter + 1
  nativeHeap := (env.nativeRefCounter + 1,NativeMutex.typeName NativeFile,
    .tuple #[.atom "unlocked",.atom "unpoisoned",NativeCodec.encode file]) :: env.nativeHeap}

inductive Reopens (path : Str) : Environment → Reply → Environment → Prop where
  | openError {before opened : Environment} (error : NativeIoError)
      (poll : NativeFile.pollOpenReadOnly path before = some (.ok (.Err error),opened))
      (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ opened.nativeRefCounter)
      (stored : opened.nativeHeap.filter (fun cell => cell.1 == error.identity) =
        [(error.identity,NativeIoError.typeName,.atom "live")]) :
      Reopens path before (.Err 3#u8) {opened with
        nativeHeap := opened.nativeHeap.filter (fun cell => cell.1 != error.identity)}
  | opened {before opened after : Environment} (file : NativeFile) (value : Reply)
      (poll : NativeFile.pollOpenReadOnly path before = some (.ok (.Ok file),opened))
      (fresh : opened.nativeHeap.any (fun cell => cell.1 == opened.nativeRefCounter + 1) = false)
      (body : Body ⟨opened.nativeRefCounter + 1⟩ (initialized file opened) value after) :
      Reopens path before value after

/-- Every admitted recovery trace executes the actual cross-crate Rust recovery,
including open failure, either critical-section error and owning cleanup. -/
theorem Reopens.ready {path : Str} {before after : Environment} {value : Reply}
    (trace : Reopens path before value after) :
    Result.ReadyPrefix (reopen_words path) before (.ok value) after := by
  rw [reopen_contract]
  cases trace with
  | openError error poll nonzero bounded stored =>
    simp only [io_core.open_readonly,monadLift_self,NativeFile.openReadOnly,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ poll
    simp only [Result.ok_bind]
    have cleanup := (NativeIoError.dispose_prefix error _ nonzero bounded stored).bind
      (fun _ => NativeM.ok (core.result.Result.Err 3#u8 : Reply))
    simpa only [Result.ok_bind,NativeM.ok] using cleanup
  | opened file value poll fresh bodyTrace =>
    simp only [io_core.open_readonly,monadLift_self,NativeFile.openReadOnly,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ poll
    simp only [Result.ok_bind]
    apply ((NativeMutex.new_prefix file _ fresh).bind _).trans
    simpa only [Result.ok_bind,initialized] using bodyTrace.ready

theorem Reopens.every_run {path : Str} {before after : Environment} {value : Reply}
    (trace : Reopens path before value after) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start before (reopen_words path) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) : outcome = .ok value :=
  trace.ready.returns elapsed run terminal

/-- Completion retains the exact final environment, not only the returned value. -/
theorem Reopens.every_final_state {path : Str} {before after : Environment} {value : Reply}
    (trace : Reopens path before value after) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start before (reopen_words path) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) :
    last = .start after (.ok value) elapsed ∧ outcome = .ok value := by
  obtain ⟨rest,executed⟩ := trace.ready.terminalRun elapsed run terminal
  cases executed with
  | refl => exact ⟨rfl,terminal.outcome_eq.symm⟩
  | step step _ =>
    simp [Concurrent.Step,Concurrent.Config.successors,Concurrent.isRequest] at step

inductive Scenario where
  | complete | empty | tail | openError | firstError | secondError | closeError
  deriving DecidableEq

@[expose] def data : Scenario → ByteArray
  | .empty => ⟨#[]⟩
  | .tail => ⟨#[7,8,9]⟩
  | _ => ⟨#[7,8,9,10]⟩
@[expose] def hasError : Scenario → Bool
  | .openError | .firstError | .secondError => true
  | _ => false
@[expose] def mask (scenario : Scenario) : ByteArray := ⟨(data scenario).data.map (fun _ => 0)⟩
@[expose] def action (scenario : Scenario) (op : String) (success : Bool) (value : Nat)
    (rest : Term) : Term := .cons (.tuple #[.atom op,.atom (if success then "ok" else "error"),
      .integer value,.bitstring (mask scenario) 0]) rest
@[expose] def closing (scenario : Scenario) : Term :=
  action scenario "close" (match scenario with | .closeError => false | _ => true) 0 .nil
@[expose] def secondScript (scenario : Scenario) : Term :=
  action scenario "seek" true 0 (match scenario with
    | .empty => action scenario "read" true 0 (closing scenario)
    | .tail => action scenario "read" true 1 (action scenario "read" true 0 (closing scenario))
    | .secondError => action scenario "read" false 2 (closing scenario)
    | _ => action scenario "read" true 1 (action scenario "read" true 1 (closing scenario)))
@[expose] def firstAfterScript (scenario : Scenario) : Term :=
  match scenario with | .firstError => closing scenario | _ => secondScript scenario
@[expose] def firstReads (scenario : Scenario) : Term :=
  match scenario with
  | .empty => action scenario "read" true 0 (secondScript scenario)
  | .firstError => action scenario "read" false 2 (closing scenario)
  | _ => action scenario "read" true 1 (action scenario "read" true 1 (secondScript scenario))
@[expose] def script (scenario : Scenario) : Term :=
  action scenario "seek" true 0 (firstReads scenario)
@[expose] def path : Str := toStr "journal"
@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : NativeFile.Names := [(fileName,1)]
@[expose] def opening (scenario : Scenario) : Term :=
  .cons (.tuple #[.atom "open",.bitstring fileName 0,
    .atom (match scenario with | .openError => "error" | _ => "ok"),
    .integer (match scenario with | .openError => 2 | _ => 0),script scenario]) .nil
@[expose] def initial (registry : List String) (counter : Nat) (scenario : Scenario) : Environment := {
  nativeResourceTypes := registry
  nativeRefCounter := counter
  nativeHeap := [
    (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],opening scenario⟩),
    (1,NativeFile.inodeTypeName,NativeFile.encode ⟨data scenario,data scenario,0,.nil⟩)] ++
    (if hasError scenario then [(2,NativeIoError.typeName,.atom "live")] else []) }

@[expose] def file (counter : Nat) : NativeFile := ⟨counter+1⟩
@[expose] def mutex (counter : Nat) : NativeMutex NativeFile := ⟨counter+2⟩
@[expose] def baseHeap (scenario : Scenario) : List (Nat × String × Term) := [
  (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],.nil⟩),
  (1,NativeFile.inodeTypeName,NativeFile.encode ⟨data scenario,data scenario,0,.nil⟩)]
@[expose] def errorHeap (live : Bool) : List (Nat × String × Term) :=
  if live then [(2,NativeIoError.typeName,.atom "live")] else []
@[expose] def opened (registry : List String) (counter : Nat) (scenario : Scenario) : Environment := {
  nativeResourceTypes := registry
  nativeRefCounter := counter+1
  nativeHeap := (counter+1,NativeFile.handleTypeName,NativeFile.encodeHandle ⟨1,0,script scenario⟩) ::
    baseHeap scenario ++ errorHeap (hasError scenario) }
@[expose] def allocated (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  initialized (file counter) (opened registry counter scenario)
@[expose] def guard (counter : Nat) (second : Bool) : NativeGuard NativeFile :=
  ⟨mutex counter,counter+(if second then 4 else 3),({} : Environment).currentPid,file counter⟩
/-- Flat witness states. Every boundary is justified below by its executable poll. -/
@[expose] def world (registry : List String) (counter : Nat) (scenario : Scenario) (used : Nat) (held : Bool)
    (position : Nat) (rest : Term) (errorLive closed : Bool := false) : Environment := {
  nativeResourceTypes := registry
  nativeRefCounter := counter+used
  nativeHeap := [
    (counter+2,NativeMutex.typeName NativeFile,
      if held then NativeMutex.lockedContents ({} : Environment).currentPid (counter+used) false (file counter)
      else .tuple #[.atom "unlocked",.atom "unpoisoned",NativeCodec.encode (file counter)]),
    (counter+1,(if closed then NativeFile.closedHandleTypeName else NativeFile.handleTypeName),
      NativeFile.encodeHandle ⟨1,position,rest⟩)] ++ baseHeap scenario ++ errorHeap errorLive }
@[expose] def firstPosition : Scenario → Nat
  | .empty | .firstError => 0
  | _ => 2
@[expose] def firstAcquired (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 3 true 0 (script scenario) (hasError scenario)
@[expose] def output : Scenario → Reply
  | .empty => .Ok (none,none)
  | .tail => .Ok (some (GuardedRecovery.ReadTrace.word 7#u8 8#u8),none)
  | .openError => .Err 3#u8
  | .firstError | .secondError => .Err 1#u8
  | _ => .Ok (some (GuardedRecovery.ReadTrace.word 7#u8 8#u8),
      some (GuardedRecovery.ReadTrace.word 9#u8 10#u8))

@[expose] def firstSought (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 3 true 0 (firstReads scenario) (hasError scenario)
@[expose] def firstReadAfter (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 3 true (firstPosition scenario) (firstAfterScript scenario) (hasError scenario)
@[expose] def firstMiddle (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 3 true 1 (action scenario "read" true 1 (secondScript scenario)) (hasError scenario)
@[expose] def firstReply : Scenario → core.result.Result (Option U16) U8
  | .firstError => .Err 1#u8
  | .empty => .Ok none
  | _ => .Ok (some (GuardedRecovery.ReadTrace.word 7#u8 8#u8))
@[expose] def firstNativeReply : Scenario → core.result.Result (Option U16) NativeIoError
  | .firstError => .Err ⟨2⟩
  | .empty => .Ok none
  | _ => .Ok (some (GuardedRecovery.ReadTrace.word 7#u8 8#u8))
@[expose] def firstUnlocked (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 3 false (firstPosition scenario) (firstAfterScript scenario)
    (match scenario with | .secondError => true | _ => false)

open scoped Lynx.NativeArithmetic

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem first_reads (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) :
    GuardedRecovery.ReadTrace.Reads (file counter) (firstSought registry counter scenario)
      (firstNativeReply scenario) (firstReadAfter registry counter scenario) := by
  cases scenario with
  | openError => exact False.elim (opening rfl)
  | empty => apply GuardedRecovery.ReadTrace.Reads.firstEof; cbv
  | firstError => apply GuardedRecovery.ReadTrace.Reads.firstError ⟨2⟩; cbv
  | complete =>
    apply GuardedRecovery.ReadTrace.Reads.complete
      (middle := firstMiddle registry counter .complete) 7#u8 8#u8 <;> cbv
  | tail =>
    apply GuardedRecovery.ReadTrace.Reads.complete
      (middle := firstMiddle registry counter .tail) 7#u8 8#u8 <;> cbv
  | secondError =>
    apply GuardedRecovery.ReadTrace.Reads.complete
      (middle := firstMiddle registry counter .secondError) 7#u8 8#u8 <;> cbv
  | closeError =>
    apply GuardedRecovery.ReadTrace.Reads.complete
      (middle := firstMiddle registry counter .closeError) 7#u8 8#u8 <;> cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem first_finish (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) :
    GuardedRecovery.ReadTrace.Finished (guard counter false) (firstNativeReply scenario)
      (firstReadAfter registry counter scenario) (firstReply scenario) (firstUnlocked registry counter scenario) := by
  cases scenario with
  | openError => exact False.elim (opening rfl)
  | firstError =>
    apply GuardedRecovery.ReadTrace.Finished.error ⟨2⟩
    · decide
    · apply of_decide_eq_true
      cbv
    · cbv
    · cbv
  | complete | empty | tail | secondError | closeError =>
    apply GuardedRecovery.ReadTrace.Finished.success _
    cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem first_locked (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) :
    Locked (mutex counter) 0#u64 (allocated registry counter scenario)
      (firstReply scenario) (firstUnlocked registry counter scenario) := by
  refine ⟨firstAcquired registry counter scenario,.Ok (guard counter false),?_,?_⟩
  · cases scenario <;> try contradiction
    all_goals cbv
  · apply GuardedRecovery.ReadTrace.Critical.read (sought := firstSought registry counter scenario)
      (readAfter := firstReadAfter registry counter scenario) 0#u64 (firstNativeReply scenario) (firstReply scenario)
    · cases scenario <;> try contradiction
      all_goals cbv
    · exact first_reads registry counter scenario positive opening
    · exact first_finish registry counter scenario positive opening

@[expose] def secondReads (scenario : Scenario) : Term :=
  match scenario with
  | .empty => action scenario "read" true 0 (closing scenario)
  | .tail => action scenario "read" true 1 (action scenario "read" true 0 (closing scenario))
  | .secondError => action scenario "read" false 2 (closing scenario)
  | _ => action scenario "read" true 1 (action scenario "read" true 1 (closing scenario))
@[expose] def secondAcquired (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 4 true (firstPosition scenario) (secondScript scenario)
    (match scenario with | .secondError => true | _ => false)
@[expose] def secondSought (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 4 true 2 (secondReads scenario)
    (match scenario with | .secondError => true | _ => false)
@[expose] def secondPosition : Scenario → Nat
  | .empty | .secondError => 2
  | .tail => 3
  | _ => 4
@[expose] def secondReadAfter (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 4 true (secondPosition scenario) (closing scenario)
    (match scenario with | .secondError => true | _ => false)
@[expose] def secondMiddle (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 4 true 3
    (action scenario "read" true (match scenario with | .tail => 0 | _ => 1) (closing scenario))
@[expose] def secondReply : Scenario → core.result.Result (Option U16) U8
  | .empty | .tail => .Ok none
  | .secondError => .Err 1#u8
  | _ => .Ok (some (GuardedRecovery.ReadTrace.word 9#u8 10#u8))
@[expose] def secondNativeReply : Scenario → core.result.Result (Option U16) NativeIoError
  | .empty | .tail => .Ok none
  | .secondError => .Err ⟨2⟩
  | _ => .Ok (some (GuardedRecovery.ReadTrace.word 9#u8 10#u8))
@[expose] def secondUnlocked (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario 4 false (secondPosition scenario) (closing scenario)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem second_reads (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) (first : scenario ≠ .firstError) :
    GuardedRecovery.ReadTrace.Reads (file counter) (secondSought registry counter scenario)
      (secondNativeReply scenario) (secondReadAfter registry counter scenario) := by
  cases scenario with
  | openError => exact False.elim (opening rfl)
  | firstError => exact False.elim (first rfl)
  | empty => apply GuardedRecovery.ReadTrace.Reads.firstEof; cbv
  | tail =>
    apply GuardedRecovery.ReadTrace.Reads.secondEof (middle := secondMiddle registry counter .tail) 9#u8 <;> cbv
  | secondError => apply GuardedRecovery.ReadTrace.Reads.firstError ⟨2⟩; cbv
  | complete =>
    apply GuardedRecovery.ReadTrace.Reads.complete (middle := secondMiddle registry counter .complete) 9#u8 10#u8 <;> cbv
  | closeError =>
    apply GuardedRecovery.ReadTrace.Reads.complete (middle := secondMiddle registry counter .closeError) 9#u8 10#u8 <;> cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem second_finish (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) (first : scenario ≠ .firstError) :
    GuardedRecovery.ReadTrace.Finished (guard counter true) (secondNativeReply scenario)
      (secondReadAfter registry counter scenario) (secondReply scenario) (secondUnlocked registry counter scenario) := by
  cases scenario with
  | openError => exact False.elim (opening rfl)
  | firstError => exact False.elim (first rfl)
  | secondError =>
    apply GuardedRecovery.ReadTrace.Finished.error ⟨2⟩
    · decide
    · change 2 ≤ counter + 4
      omega
    · cbv
    · cbv
  | complete | empty | tail | closeError =>
    apply GuardedRecovery.ReadTrace.Finished.success _
    cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem second_locked (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) (first : scenario ≠ .firstError) :
    Locked (mutex counter) 2#u64 (firstUnlocked registry counter scenario)
      (secondReply scenario) (secondUnlocked registry counter scenario) := by
  refine ⟨secondAcquired registry counter scenario,.Ok (guard counter true),?_,?_⟩
  · cases scenario <;> try contradiction
    all_goals cbv
  · apply GuardedRecovery.ReadTrace.Critical.read (sought := secondSought registry counter scenario)
      (readAfter := secondReadAfter registry counter scenario) 2#u64 (secondNativeReply scenario) (secondReply scenario)
    · cases scenario <;> try contradiction
      all_goals cbv
    · exact second_reads registry counter scenario positive opening first
    · exact second_finish registry counter scenario positive opening first

@[expose] def readEnd (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  match scenario with | .firstError => firstUnlocked registry counter scenario | _ => secondUnlocked registry counter scenario
@[expose] def used : Scenario → Nat
  | .firstError => 3
  | _ => 4
@[expose] def endPosition : Scenario → Nat
  | .firstError => 0
  | other => secondPosition other
@[expose] def closed (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  world registry counter scenario (used scenario) false (endPosition scenario) .nil false true
@[expose] def done (registry : List String) (counter : Nat) (scenario : Scenario) : Environment := {
  closed registry counter scenario with
  nativeHeap := (closed registry counter scenario).nativeHeap.filter (fun cell => cell.1 != (mutex counter).id) }

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem owning_cleanup (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) :
    Cleanup (mutex counter) (readEnd registry counter scenario) (done registry counter scenario) := by
  apply Cleanup.close (file counter) false _ (closed registry counter scenario)
  all_goals cases scenario <;> try contradiction
  all_goals cbv

@[expose] def firstValue : Scenario → Option U16
  | .empty => none
  | _ => some (GuardedRecovery.ReadTrace.word 7#u8 8#u8)

theorem admitted_body (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (opening : scenario ≠ .openError) :
    Body (mutex counter) (allocated registry counter scenario) (output scenario) (done registry counter scenario) := by
  by_cases first : scenario = .firstError
  · subst scenario
    exact .firstError 1#u8 (first_locked registry counter .firstError positive (by decide))
      (owning_cleanup registry counter .firstError positive (by decide))
  · have firstOk : firstReply scenario = .Ok (firstValue scenario) := by
      cases scenario <;> try contradiction
      all_goals rfl
    have returned : pairReply (firstValue scenario) (secondReply scenario) = output scenario := by
      cases scenario <;> try contradiction
      all_goals rfl
    rw [← returned]
    apply Body.second (firstValue scenario) (secondReply scenario)
    · simpa only [firstOk] using first_locked registry counter scenario positive opening
    · exact second_locked registry counter scenario positive opening first
    · have finish := owning_cleanup registry counter scenario positive opening
      cases scenario <;> try contradiction
      all_goals exact finish

@[expose] def failedOpen (registry : List String) (counter : Nat) : Environment := {
  nativeResourceTypes := registry
  nativeRefCounter := counter
  nativeHeap := baseHeap .openError ++ errorHeap true }
@[expose] def finalState (registry : List String) (counter : Nat) (scenario : Scenario) : Environment :=
  if scenario = .openError then {nativeResourceTypes := registry,nativeRefCounter := counter,nativeHeap := baseHeap .openError}
  else done registry counter scenario

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
/-- Concrete witnesses cover every recovery control-flow branch, including
truncation and ignored close errors, without enumerating freshness counters. -/
theorem admitted_recovery (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter) :
    Reopens path (initial registry counter scenario) (output scenario) (finalState registry counter scenario) := by
  by_cases failure : scenario = .openError
  · subst scenario
    change Reopens path (initial registry counter .openError) (.Err 3#u8)
      {nativeResourceTypes := registry,nativeRefCounter := counter,nativeHeap := baseHeap .openError}
    apply Reopens.openError (opened := failedOpen registry counter) ⟨2⟩
    · cbv
    · decide
    · exact positive
    · cbv
  · simp only [finalState,failure,↓reduceIte]
    apply Reopens.opened (opened := opened registry counter scenario) (file counter) (output scenario)
    · cases scenario <;> try contradiction
      all_goals cbv
    · cases scenario <;> try contradiction
      all_goals cbv
    · simpa only [opened,allocated,mutex] using admitted_body registry counter scenario positive failure

/-- The witnessed traces give a direct implementation-linked execution theorem,
so reporting need not treat a trace predicate as a verified Rust implementation. -/
theorem admitted_execution (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter) :
    Result.ReadyPrefix (reopen_words path) (initial registry counter scenario)
      (.ok (output scenario)) (finalState registry counter scenario) :=
  (admitted_recovery registry counter scenario positive).ready

/-- Every terminal native run in each witnessed scenario has the exact owner,
error-capability, namespace, inode and descriptor poststate. -/
theorem admitted_every_run (registry : List String) (counter : Nat) (scenario : Scenario) (positive : 2 ≤ counter)
    (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start (initial registry counter scenario) (reopen_words path) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) :
    last = .start (finalState registry counter scenario) (.ok (output scenario)) elapsed ∧
      outcome = .ok (output scenario) :=
  (admitted_recovery registry counter scenario positive).every_final_state elapsed run terminal

@[expose] def firstFailureBoot : Environment := initial [] 12 .firstError
@[expose] def secondFailureBoot : Environment := initial [] 12 .secondError
@[expose] def tailBoot : Environment := initial [] 12 .tail

end GuardedRecovery.RecoveryTrace
