module
public import Positional.Properties
public import Positional.RustlerBridge
import Lynx.Runner.CheckPost
public section
open Aeneas Aeneas.Std Lynx
open Lynx.NativeFile Positional.Properties
namespace Positional.Nif

abbrev Payload := io_native.offset_file.OffsetFile

@[expose] def resource : Payload := ⟨⟨1⟩⟩
@[expose] def reference : Term := .nativeReference 5
@[expose] def original : ByteArray := ⟨#[1, 2]⟩
@[expose] def patched : ByteArray := ⟨#[1, 2, 0, 0, 9]⟩
@[expose] def zeros (data : ByteArray) : ByteArray := ⟨_root_.Array.replicate data.size 0⟩

@[expose] def successScript : Term :=
  outcome "write_at" true 1 (zeros original) <|
  outcome "sync_data" true 0 ByteArray.empty <|
  outcome "read_at" true 1 (zeros patched) <|
  outcome "read_at" true 0 (zeros patched) <|
  outcome "read_at" true 1 (zeros patched) .nil

@[expose] def shortScript : Term :=
  outcome "write_at" true 0 (zeros original) <|
  outcome "sync_data" true 0 ByteArray.empty <|
  outcome "read_at" true 1 (zeros original) .nil

@[expose] def seed (script : Term) : Environment :=
  { ({} : Environment).setPdict [(.atom "slots", reference)] with
    nativeRefCounter := 5
    nativeResourceTypes := [NativeResourceArc.typeName Payload]
    nativeHeap := NativeResourceArc.vmCells resource 2 4 5 ++
      [(1, typeName, encode ⟨original, original, 1, script⟩)] }

@[expose] def ready : Environment := seed successScript
@[expose] def short : Environment := seed shortScript

/-- Check the post-call heap, the single retained VM pin and an admitted crash
image. No decoded call owner remains in the heap. -/
@[expose] def accepted (contents : ByteArray) (pending : Term) (acquisitions : Nat)
    (config : Concurrent.Config Term) : Bool :=
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  let heap := NativeResourceArc.vmCells resource 2 4 5 ++
    [(1, typeName, encode ⟨contents, contents, 1, pending⟩)]
  config.outcome.isTrue && env.nativeRefCounter == 5 + acquisitions &&
    heap.all env.nativeHeap.contains && env.nativeHeap.length == heap.length &&
    (match crashImage ⟨1⟩ (zeros contents) env with
      | some image => image.bytes.data == contents.data
      | none => false)

theorem accepted_outcome {contents : ByteArray} {pending : Term} {acquisitions : Nat}
    {config : Concurrent.Config Term}
    (checked : accepted contents pending acquisitions config = true) :
    config.outcome = .ok Term.true := by
  apply Outcome.eq_of_isTrue
  simp only [accepted, Bool.and_eq_true] at checked
  exact checked.1.1.1.1

@[expose] def patchCall (patch : NativeResourceArc Payload → U64 → U8 → NativeM Bool)
    (offset : U64) (value : U8) : Result Term := do
  let owner ← NativeResourceArc.decode reference
  Rustler.executeNative (patch owner offset value) Rustler.encodeBool

@[expose] def observeCall (observe : NativeResourceArc Payload → U64 → NativeM (Option U8))
    (offset : U64) : Result Term := do
  let owner ← NativeResourceArc.decode reference
  Rustler.executeNative (observe owner offset) (Rustler.encodeOption Rustler.encodeUnsigned)

@[expose] def program (patch : NativeResourceArc Payload → U64 → U8 → NativeM Bool)
    (observe : NativeResourceArc Payload → U64 → NativeM (Option U8)) : Result Term := do
  let written ← patchCall patch 4#u64 9#u8
  let observed ← observeCall observe 4#u64
  let eof ← observeCall observe 5#u64
  let first ← observeCall observe 0#u64
  Result.ok (if written == Term.true && observed == .integer 9 && eof == .atom "nil" &&
    first == .integer 1 then Term.true else Term.false)

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
/-- The actual extracted NIF bodies, reached through modeled Rustler acquisition,
execution and return codecs, preserve the cursor and shared resource lifetime,
and expose the persisted patch to later reads. -/
theorem completed_program (elapsed : Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config Term) (outcome : Outcome Term)
    (run : Concurrent.Run (.start ready (program __PATCH__ __OBSERVE__) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) :
    accepted patched .nil 4 last = true := by
  apply Concurrent.checkPost_sound (depth := 256) ?_ run terminal
  clear events last outcome run terminal
  lynx_check_post

end Positional.Nif
