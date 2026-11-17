module
public import Positional.Nif
import Lynx.Runner.CheckPost
public section
open Aeneas Aeneas.Std Lynx NativeFile
open Positional.Nif (Payload original patched zeros)
namespace Positional.Opened

@[expose] def fileName : ByteArray := ⟨#[115, 108, 111, 116, 115]⟩

@[expose] def openChoice (success : Bool) (error : Nat) (script rest : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring fileName 0, .atom (if success then "ok" else "error"),
    .integer error, script]) rest

@[expose] def namespaceCell (names : Names) (script : Term) : Nat × String × Term :=
  (0, namespaceTypeName, encodeNamespace ⟨names, names, [], script⟩)

@[expose] def inodeCell (contents : ByteArray) : Nat × String × Term :=
  (1, inodeTypeName, encode ⟨contents, contents, 0, .nil⟩)

@[expose] def names : Names := [(fileName, 1)]

@[expose] def ready : Environment :=
  let writer := Positional.Properties.outcome "write_at" true 1 (zeros original) <|
    Positional.Properties.outcome "sync_data" true 0 ByteArray.empty .nil
  let reader := Positional.Properties.outcome "read_at" true 1 (zeros patched) .nil
  { nativeRefCounter := 1
    nativeResourceTypes := [NativeResourceArc.typeName Payload]
    nativeHeap := [namespaceCell names (openChoice true 0 writer (openChoice true 0 reader .nil)),
      inodeCell original] }

@[expose] def missing : Environment :=
  { nativeRefCounter := 1
    nativeResourceTypes := [NativeResourceArc.typeName Payload]
    nativeHeap := [namespaceCell [] (openChoice false 1 .nil .nil),
      (1, NativeIoError.typeName, .atom "live")] }

@[expose] def openedHeap : List (Nat × String × Term) :=
  NativeResourceArc.vmCells (⟨⟨2⟩⟩ : Payload) 3 5 6 ++
    NativeResourceArc.vmCells (⟨⟨7⟩⟩ : Payload) 8 10 11 ++
    [(2, writableHandleTypeName, encodeHandle ⟨1, 0, .nil⟩),
     (7, writableHandleTypeName, encodeHandle ⟨1, 0, .nil⟩),
     namespaceCell names .nil, inodeCell patched]

/-- Check the exact live cells and owner allocation count. Both descriptors
have their own cursor and drained script, and reference a single inode. -/
@[expose] def accepted (counter : Nat) (heap : List (Nat × String × Term))
    (config : Concurrent.Config Term) : Bool :=
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  config.outcome.isTrue && env.nativeRefCounter == counter &&
    heap.all env.nativeHeap.contains && env.nativeHeap.length == heap.length

theorem accepted_outcome {counter : Nat} {heap : List (Nat × String × Term)}
    {config : Concurrent.Config Term} (checked : accepted counter heap config = true) :
    config.outcome = .ok Term.true := by
  apply Outcome.eq_of_isTrue
  simp only [accepted, Bool.and_eq_true] at checked
  exact checked.1.1.1

abbrev Opener := NativeM (core.result.Result (NativeResourceArc Payload) Rustler.DecoderError)

@[expose] def openCall (opener : Opener) : Result Term :=
  Rustler.withNativeResult opener fun owner =>
    Rustler.executeNative (do
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      Result.ok term) id

@[expose] def program (opener : Opener)
    (patch : NativeResourceArc Payload → U64 → U8 → NativeM Bool)
    (observe : NativeResourceArc Payload → U64 → NativeM (Option U8)) : Result Term := do
  let writer ← openCall opener
  let reader ← openCall opener
  let writerOwner ← NativeResourceArc.decode writer
  let wrote ← Rustler.executeNative (patch writerOwner 4#u64 9#u8) Rustler.encodeBool
  let readerOwner ← NativeResourceArc.decode reader
  let read ← Rustler.executeNative (observe readerOwner 4#u64)
    (Rustler.encodeOption Rustler.encodeUnsigned)
  Result.ok (Rustler.encodeBool (writer != reader && wrote == Term.true && read == .integer 9))

@[expose] def rejectsOpen (opener : Opener) : Result Term :=
  Result.handle (do
    let _ ← openCall opener
    Result.ok Term.false) fun error =>
      match error with
      | .error (.atom "open_failed") => Result.ok Term.true
      | _ => Result.ok Term.false

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
theorem opened_shared_inode (elapsed : Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start ready (program __OPEN__ __PATCH__ __OBSERVE__) elapsed)
      events last) (terminal : Concurrent.Terminal last outcome) :
    accepted 13 openedHeap last = true := by
  apply Concurrent.checkPost_sound (depth := 256) ?_ run terminal
  clear events last outcome run terminal
  lynx_check_post

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
theorem failed_open_releases_error (elapsed : Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start missing (rejectsOpen __OPEN__) elapsed)
      events last) (terminal : Concurrent.Terminal last outcome) :
    accepted 1 [namespaceCell [] .nil] last = true := by
  apply Concurrent.checkPost_sound (depth := 128) ?_ run terminal
  clear events last outcome run terminal
  lynx_check_post

end Positional.Opened
