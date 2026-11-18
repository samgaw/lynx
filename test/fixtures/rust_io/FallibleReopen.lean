module
public import Record.Extraction.Funs
public import Record.RustlerBridge
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.FallibleReopen
open NativeFile
open scoped Lynx.NativeArithmetic

@[expose] def journalName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def contents (left : Bool) : ByteArray :=
  if left then ⟨#[13,0,242,255,19,0,236,255]⟩ else ⟨#[13,0,242,255,23,0,232,255]⟩
@[expose] def zeroes : ByteArray := ⟨#[0,0,0,0,0,0,0,0]⟩

@[expose] def choice (op : String) (success : Bool) (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom op, .atom (if success then "ok" else "error"), .integer count, .bitstring zeroes 0]) rest

@[expose] def readBytes (count : Nat) (rest : Term) : Term :=
  (List.range count).foldr (fun _ => choice "read" true 1) rest

@[expose] def openScript (success : Bool) (error : Nat) (steps rest : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring journalName 0,
    .atom (if success then "ok" else "error"), .integer error, steps]) rest

@[expose] def capScript (closeSucceeds : Bool) : Term :=
  let close := choice "close" closeSucceeds (if closeSucceeds then 0 else 5) .nil
  choice "seek" true 0 (readBytes 8 close)

@[expose] def boot (counter : Nat) (left openSucceeds closeSucceeds : Bool) : Environment :=
  let data := contents left
  let names := [(journalName, 1)]
  let openChoice := openScript openSucceeds (if openSucceeds then 0 else counter + 1)
    (if openSucceeds then capScript closeSucceeds else .nil) .nil
  { nativeRefCounter := if openSucceeds then counter else counter + 1,
    nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource],
    nativeHeap := [
      (0, namespaceTypeName, encodeNamespace ⟨names, names, [], openChoice⟩),
      (1, inodeTypeName, encode ⟨data, data, 0, .nil⟩)] ++
        (if openSucceeds then [] else [(counter + 1, NativeIoError.typeName, .atom "live")]) }

@[expose] def call
    (reopen : U32 → NativeM (core.result.Result (NativeResourceArc shared_log.LogResource) Rustler.DecoderError))
    (limit : U32) : Result Term :=
  Rustler.withNativeResult (reopen limit) fun owner => do
    let term ← NativeResourceArc.encode owner
    NativeOwnedDrop.drop owner
    Result.ok term

@[expose] def environment : Concurrent.Config Term → Environment
  | .start env _ _ => env
  | .running state .. => state.nativeView []

@[expose] def rejected (counter : Nat) (left opened : Bool) (last : Concurrent.Config Term) : Bool :=
  let env := environment last
  match last.outcome, inode 1 env, namespaceSnapshot env with
  | .error (.error (.atom reason)), some file, some snapshot =>
    let names := [(journalName, 1)]
    reason == (if opened then "record_limit" else "journal_io") &&
    file.visible.data == (contents left).data && file.durable.data == (contents left).data &&
    tablesEqual snapshot.names names && tablesEqual snapshot.committed names &&
      snapshot.pending.isEmpty && snapshot.script == .nil &&
    (if opened then
       env.nativeRefCounter == counter + 1 && env.nativeHeap.length == 3 &&
       match getHandle ⟨counter + 1⟩ closedHandleTypeName env with
       | some handle => handle.inode == 1 && handle.position == 8 && handle.script == .nil
       | none => false
     else env.nativeRefCounter == counter + 1 && env.nativeHeap.length == 2)
  | _, _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
theorem errors_preserve_completed_records (counter : Nat) (left opened closeSucceeds : Bool)
    (positive : 1 ≤ counter) (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (rejected counter left opened) 64
      (.start (boot counter left opened closeSucceeds) (call __TRY_REOPEN__ 2#u32) elapsed) = true := by
  cases left <;> cases opened <;> cases closeSucceeds <;> cbv

@[expose] def limitedBoot : Environment := boot 1 true true true
@[expose] def failedOpenBoot : Environment := boot 1 false false true

@[expose] def lawAccepted (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom "true") => true
  | _ => false

theorem law_outcome (last : Concurrent.Config Term) (accepted : lawAccepted last = true) :
    last.outcome = .ok Term.true := by
  unfold lawAccepted at accepted
  split at accepted
  · assumption
  · contradiction

end Record.FallibleReopen
