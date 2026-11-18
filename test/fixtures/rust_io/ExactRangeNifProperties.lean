module
public import ExactWrite.Nif
public import ExactWrite.Read
public section

open Aeneas Aeneas.Std Lynx Lynx.NativeFile
open ExactWrite.Nif (Payload Patch writer ready)
namespace ExactWrite.Range

abbrev ReadWord := NativeResourceArc Payload → U64 → NativeM (Option U16)

@[expose] def program (write : Patch) (read : ReadWord) : Result Term := do
  let written ← ExactWrite.Nif.program write
  if written.identical Term.true then
    let owner ← NativeResourceArc.decode writer
    Rustler.executeNative (read owner 1#u64) (Rustler.encodeOption Rustler.encodeUnsigned)
  else
    Result.ok (.atom "write_failed")

@[expose] def readBack (cfg : Concurrent.Config Term) : Bool :=
  let world := match cfg with
    | .start env .. => env
    | .running state .. => state.nativeView []
  let complete := ExactWrite.Properties.complete
  let expected := NativeResourceArc.vmCells (⟨⟨2⟩⟩ : Payload) 3 5 6 ++ [
    (1, inodeTypeName, encode ⟨complete, complete, 0, .nil⟩),
    (2, writableHandleTypeName, encodeHandle ⟨1, 5, .nil⟩),
    (8, NativeIoError.kindTypeName, NativeIoError.kindEntry (.os 7) "Interrupted")]
  match cfg.outcome with
  | .ok value =>
    value.identical (.integer 2055) && world.nativeRefCounter == 10 &&
      world.nativeHeap.length == expected.length &&
      expected.all fun (expectedId, tag, value) =>
        world.nativeHeap.any fun (actualId, actualTag, actual) =>
          actualId == expectedId && actualTag == tag && actual.identical value
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
/-- The actual NIFs synchronize and decode the complete range. The short reads
consume their scripts while preserving the named descriptor cursor and VM pin. -/
theorem word_after_sync (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost readBack 64
      (.start ready (program __WRITE_ALL__ __READ_WORD__) elapsed) = true := by
  cbv

end ExactWrite.Range
