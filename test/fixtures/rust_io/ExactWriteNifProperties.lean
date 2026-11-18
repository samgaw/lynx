module
public import ExactWrite.Properties
public import ExactWrite.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx Lynx.NativeFile
open ExactWrite.Properties (initial complete actionChoice shortWrite)

namespace ExactWrite.Nif

abbrev Payload := io_native.offset_file.OffsetFile
abbrev Patch := NativeResourceArc Payload → U64 → Rustler.Binary → NativeM Bool

@[expose] def bytes : ByteArray := ⟨#[7, 8]⟩
@[expose] def writer : Term := .nativeReference 6

@[expose] def readTail : Term :=
  let read := actionChoice "read_at" true 1 ⟨#[0, 0, 0]⟩
  read (read .nil)

@[expose] def ready : Environment :=
  let writes := shortWrite (actionChoice "write_at" false 7 ⟨#[0, 0]⟩ (shortWrite
    (actionChoice "sync_data" true 0 ByteArray.empty readTail)))
  { ({} : Environment).setPdict [(.atom "writer", writer)] with
    nativeRefCounter := 8
    nativeResourceTypes := [NativeResourceArc.typeName Payload]
    nativeHeap := NativeResourceArc.vmCells (⟨⟨2⟩⟩ : Payload) 3 5 6 ++ [
      (1, inodeTypeName, encode ⟨initial, initial, 0, .nil⟩),
      (2, writableHandleTypeName, encodeHandle ⟨1, 5, writes⟩),
      (7, NativeIoError.typeName, .atom "live"),
      (8, NativeIoError.kindTypeName, NativeIoError.kindEntry (.os 7) "Interrupted")] }

@[expose] def program (patch : Patch) : Result Term := do
  let owner ← NativeResourceArc.decode writer
  Rustler.executeNative (patch owner 1#u64 bytes) Rustler.encodeBool

@[expose] def acknowledged (cfg : Concurrent.Config Term) : Bool :=
  let world := match cfg with
    | .start env .. => env
    | .running state .. => state.nativeView []
  let expected := NativeResourceArc.vmCells (⟨⟨2⟩⟩ : Payload) 3 5 6 ++ [
    (1, inodeTypeName, encode ⟨complete, complete, 0, .nil⟩),
    (2, writableHandleTypeName, encodeHandle ⟨1, 5, readTail⟩),
    (8, NativeIoError.kindTypeName, NativeIoError.kindEntry (.os 7) "Interrupted")]
  cfg.outcome.isTrue && world.nativeRefCounter == 9 && world.nativeHeap.length == expected.length &&
    expected.all fun (expectedId, tag, value) =>
      world.nativeHeap.any fun (actualId, actualTag, actual) =>
        actualId == expectedId && actualTag == tag && actual.identical value

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The actual binary-taking NIF acknowledges the complete durable word and
releases its temporary resource owner and the interrupted error capability. -/
theorem acknowledged_range (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost acknowledged 64
      (.start ready (program __WRITE_ALL__) elapsed) = true := by
  cbv

end ExactWrite.Nif
