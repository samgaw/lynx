module
public import Record.FallibleReopen
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.FallibleRetry
open NativeFile
open Record.FallibleReopen (journalName contents choice readBytes openScript capScript call environment)
open scoped Lynx.NativeArithmetic

@[expose] def successfulRepair : Term :=
  let finished := choice "read" true 0 (choice "set_len" true 0 (choice "sync_all" true 0 .nil))
  choice "seek" true 0 (readBytes 8 finished)

@[expose] def retryBoot (counter : Nat) (left opened closeSucceeds : Bool) : Environment :=
  let first := openScript opened (if opened then 0 else counter + 1)
    (if opened then capScript closeSucceeds else .nil) (openScript true 0 successfulRepair .nil)
  replaceNamespaceScript first (Record.FallibleReopen.boot counter left opened closeSucceeds)

@[expose] def expectedReason (opened : Bool) : String := if opened then "record_limit" else "journal_io"

@[expose] def retry
    (reopen : U32 → NativeM (core.result.Result (NativeResourceArc shared_log.LogResource) Rustler.DecoderError))
    (opened : Bool) : Result Term := do
  let failed ← Result.handle
    (do let _ ← call reopen 2#u32; Result.ok false)
    (fun error => match error with
      | .error (.atom reason) => .ok (reason == expectedReason opened)
      | _ => .ok false)
  if failed then call reopen 3#u32 else .error .exhausted

@[expose] def retryState (counter : Nat) (left opened : Bool) (pin : Nat) (last : Concurrent.Config Term) : Bool :=
  let env := environment last
  match getHandle ⟨counter + 2⟩ writableHandleTypeName env,
      inode 1 env, namespaceSnapshot env with
  | some handle, some file, some table =>
    let names := [(journalName, 1)]
    let payload : shared_log.LogResource := ⟨⟨counter + 3⟩⟩
    pin == counter + 7 && env.nativeRefCounter == pin &&
    handle.inode == 1 && handle.position == 8 && handle.script == .nil &&
    file.visible.data == (contents left).data && file.durable.data == (contents left).data &&
    tablesEqual table.names names && tablesEqual table.committed names &&
    table.pending.isEmpty && table.script == .nil &&
    (NativeResourceArc.vmCells payload (counter + 4) (counter + 6) pin).all env.nativeHeap.contains &&
    env.nativeHeap.contains (counter + 3, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference (counter + 2)]) &&
    !env.nativeHeap.any (fun cell => cell.1 == counter + 5) &&
    (if opened then
      match getHandle ⟨counter + 1⟩ closedHandleTypeName env with
      | some old => old.inode == 1 && old.position == 8 && old.script == .nil
      | none => false
    else !env.nativeHeap.any (fun cell => cell.1 == counter + 1))
  | _, _, _ => false

@[expose] def succeeded (counter : Nat) (left opened : Bool) (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.nativeReference pin) => retryState counter left opened pin last
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
/-- A retry after either typed failure returns a fresh writable VM resource for the same
durable journal. The old descriptor or error capability cannot survive as a live owner. -/
theorem reopens_after_typed_failure (counter : Nat) (left opened closeSucceeds : Bool)
    (positive : 1 ≤ counter) (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (succeeded counter left opened) 128
      (.start (retryBoot counter left opened closeSucceeds)
        (retry __TRY_REOPEN__ opened) elapsed) = true := by
  cases left <;> cases opened <;> cases closeSucceeds <;> cbv

@[expose] def limitedRetry : Environment := retryBoot 1 true true true
@[expose] def failedOpenRetry : Environment := retryBoot 1 false false true

@[expose] def lawAccepted (opened : Bool) (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom "true") => retryState 1 opened opened 8 last
  | _ => false

theorem law_outcome (opened : Bool) (last : Concurrent.Config Term)
    (accepted : lawAccepted opened last = true) : last.outcome = .ok Term.true := by
  unfold lawAccepted at accepted
  split at accepted
  · assumption
  · contradiction

end Record.FallibleRetry
