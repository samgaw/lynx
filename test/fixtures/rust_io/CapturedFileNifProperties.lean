module
public import Lynx
public import CapturedFile.Properties
public import CapturedFile.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace CapturedFile.NifProperties
open NativeFile

theorem facade_contract (input : Rustler.Binary) (accepted : Bool) :
    __WRITE__ input accepted = (do
      let opened ← io_protocol.open_readwrite (toStr "journal")
      match opened with
      | .Ok file => do
        let bytes ← NativeM.fromRust (Rustler.binaryAsSlice input)
        let result ← io_protocol.checked_write file bytes accepted
        match result with
        | .Err () => NativeM.ok (.Err ())
        | .Ok (.Err error) => NativeM.ok (.Ok (.Err error))
        | .Ok (.Ok count) => do
          let wide ← NativeM.lift (UScalar.cast .U64 count)
          NativeM.ok (.Ok (.Ok wide))
      | .Err error => do
        NativeIoError.dispose error
        NativeM.ok (.Ok (.Err 2#u8))) := by
  simp [__WRITE__, NativeOwnedDrop.drop, NativeM.ok]
  congr 1
  funext opened
  cases opened <;> simp
  congr 1
  funext bytes
  congr 1
  funext result
  cases result with
  | Err panic => cases panic; rfl
  | Ok reply => cases reply <;> rfl

@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : Names := [(fileName, 1)]
@[expose] def opening (success : Bool) (error : Nat) (script : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring fileName 0,
    .atom (if success then "ok" else "error"), .integer error, script]) .nil
@[expose] def ioScript : Term :=
  Properties.outcome "write" true 2 ⟨#[0]⟩
    (Properties.outcome "close" false 0 ⟨#[0]⟩ .nil)
@[expose] def initial : Environment := {
  nativeRefCounter := 1
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], opening true 0 ioScript⟩),
    (1, inodeTypeName, encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, .nil⟩)] }
@[expose] def rejected : Environment := {
  nativeRefCounter := 2
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨[], [], [], opening false 2 .nil⟩),
    (2, NativeIoError.typeName, .atom "live")] }

@[expose] def retained (accepted : Bool)
    (config : Concurrent.Config (core.result.Result (core.result.Result U64 U8) Unit)) : Bool :=
  let result := match config.outcome with
    | .ok (.Ok (.Ok count)) => accepted && count.val == 2
    | .ok (.Err ()) => !accepted
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  result && match inode 1 env, lookupClosed ⟨2⟩ env with
    | some disk, some closed =>
      disk.visible.data == #[7,8] && disk.durable.data == #[1] &&
        closed.position == 2 && (lookup ⟨2⟩ env).isNone
    | _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem retains_write_without_sync (accepted : Bool) :
    Concurrent.checkPost (retained accepted) 128
      (.start initial (__WRITE__ ⟨#[7,8]⟩ accepted)) = true := by
  cases accepted <;> cbv

theorem every_completed_call (accepted : Bool)
    (run : Concurrent.Run (.start initial (__WRITE__ ⟨#[7,8]⟩ accepted)) events last)
    (terminal : Concurrent.Terminal last outcome) : retained accepted last = true :=
  Concurrent.checkPost_sound (retains_write_without_sync accepted) run terminal

@[expose] def errorRetired
    (config : Concurrent.Config (core.result.Result (core.result.Result U64 U8) Unit)) : Bool :=
  match config.outcome with
  | .ok (.Ok (.Err error)) =>
    let env := match config with
      | .start env .. => env
      | .running state .. => state.nativeView []
    error.val == 2 && !(env.nativeHeap.any (fun cell => cell.1 == 2))
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem opening_error_consumes_payload (accepted : Bool) :
    Concurrent.checkPost errorRetired 128
      (.start rejected (__WRITE__ ⟨#[7,8]⟩ accepted)) = true := by
  cases accepted <;> cbv

end CapturedFile.NifProperties
