module
public import Lynx
public import FileAwait.Properties
public import FileAwait.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace FileAwait.NifProperties
open NativeFile

theorem facade_contract (first second : U8) (resume : Bool) :
    __WRITE__ first second resume = (do
      let opened ← io_protocol.open_readwrite (toStr "journal")
      match opened with
      | .Ok file => do
        let result ← io_protocol.poll_write file (Array.make 2#usize [first, second]) resume
        match result with
        | none => NativeM.ok (.Ok none)
        | some (.Err error) => NativeM.ok (.Err error)
        | some (.Ok count) => NativeM.ok (.Ok (some (UScalar.cast .U64 count)))
      | .Err error => do
        NativeIoError.dispose error
        NativeM.ok (.Err 2#u8)) := by
  simp [__WRITE__, NativeOwnedDrop.drop, NativeM.ok, NativeM.lift]
  congr 1
  funext opened
  cases opened <;> simp
  congr 1
  funext result
  cases result with
  | none => rfl
  | some reply => cases reply <;> rfl

@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : Names := [(fileName, 1)]
@[expose] def opening (success : Bool) (error : Nat) (script : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring fileName 0,
    .atom (if success then "ok" else "error"), .integer error, script]) .nil
@[expose] def script : Term :=
  Properties.outcome "write" true 2 (Properties.outcome "close" false 0 .nil)
@[expose] def initial : Environment := {
  nativeRefCounter := 1
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], opening true 0 script⟩),
    (1, inodeTypeName, encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, .nil⟩)] }
@[expose] def rejected : Environment := {
  nativeRefCounter := 2
  nativeHeap := [
    (0, namespaceTypeName, encodeNamespace ⟨[], [], [], opening false 2 .nil⟩),
    (2, NativeIoError.typeName, .atom "live")] }

@[expose] def retained (resume : Bool)
    (config : Concurrent.Config (core.result.Result (Option U64) U8)) : Bool :=
  let result := match config.outcome with
    | .ok (.Ok (some count)) => resume && count.val == 2
    | .ok (.Ok none) => !resume
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
theorem cancellation_and_completion_close (resume : Bool) :
    Concurrent.checkPost (retained resume) 256
      (.start initial (__WRITE__ 7#u8 8#u8 resume)) = true := by
  set_option cbv.maxSteps 8000000 in cases resume <;> cbv

theorem every_completed_call (resume : Bool)
    (run : Concurrent.Run (.start initial (__WRITE__ 7#u8 8#u8 resume)) events last)
    (terminal : Concurrent.Terminal last outcome) : retained resume last = true :=
  Concurrent.checkPost_sound (cancellation_and_completion_close resume) run terminal

@[expose] def errorRetired
    (config : Concurrent.Config (core.result.Result (Option U64) U8)) : Bool :=
  match config.outcome with
  | .ok (.Err error) =>
    let env := match config with
      | .start env .. => env
      | .running state .. => state.nativeView []
    error.val == 2 && !(env.nativeHeap.any (fun cell => cell.1 == 2))
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem opening_error_consumes_payload (resume : Bool) :
    Concurrent.checkPost errorRetired 256
      (.start rejected (__WRITE__ 7#u8 8#u8 resume)) = true := by
  cases resume <;> cbv

end FileAwait.NifProperties
