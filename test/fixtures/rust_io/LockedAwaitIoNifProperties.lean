module
public import Lynx
public import LockedAwait.NifProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace LockedAwait.IoNif

theorem readonly_contract : __READONLY__ = (do
    let opened ← io_protocol.open_readonly (toStr "journal")
    match opened with
    | .Ok file => do
      let mutex ← NativeMutex.new file
      let owner ← NativeResourceArc.newOwned ({file := mutex} : shared_log.LogResource)
      NativeM.ok (.Ok owner)
    | .Err error => do
      NativeIoError.dispose error
      NativeM.ok (.Err (Rustler.atomErrorOutcome "open_failed"))) := by
  simp [__READONLY__, NativeOwnedDrop.drop, NativeM.ok,
    LockedAwait.Extraction.ErrorConstants.literal_0]
  rfl

@[expose] def action (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if success then "ok" else "error"),
    .integer value, .bitstring mask 0]) rest
@[expose] def readWord (mask : ByteArray) (rest : Term) : Term :=
  action "seek" true 0 mask (action "read" true 1 mask (action "read" true 1 mask rest))
@[expose] def errorsScript : Term :=
  action "write" false 2 ⟨#[0,0]⟩ (action "write" false 3 ⟨#[0,0]⟩
    (readWord ⟨#[0,0]⟩ .nil))
@[expose] def decodeScript : Term :=
  action "write" false 2 ⟨#[0,0]⟩ (readWord ⟨#[0,0]⟩ .nil)
@[expose] def partialScript : Term :=
  action "write" true 1 ⟨#[0]⟩ (action "write" true 2 ⟨#[0]⟩
    (readWord ⟨#[0]⟩ (action "seek" true 0 ⟨#[0]⟩
      (action "read" true 1 ⟨#[0]⟩ (action "read" true 0 ⟨#[0]⟩ .nil)))))
@[expose] def initial (counter : Nat) (bytes : ByteArray) (script : Term)
    (errors : List Nat) : Environment := {
  nativeRefCounter := counter
  nativeHeap := [
    (0, NativeFile.namespaceTypeName,
      NativeFile.encodeNamespace ⟨NifProperties.names, NifProperties.names, [],
        .cons (.tuple #[.atom "open", .bitstring NifProperties.fileName 0,
          .atom "ok", .integer 0, script]) .nil⟩),
    (1, NativeFile.inodeTypeName, NativeFile.encode ⟨bytes, bytes, 0, .nil⟩)] ++
    errors.map (fun identity => (identity, NativeIoError.typeName, .atom "live")) }
@[expose] def readOnly : Environment := initial 3 ⟨#[7,8]⟩ errorsScript [2,3]
@[expose] def decoding : Environment := initial 2 ⟨#[7,8]⟩ decodeScript [2]
@[expose] def shortWrite : Environment := initial 1 ⟨#[1]⟩ partialScript []
/-- Error results without admitted callback-free payload capabilities cannot
establish a successful native execution. -/
@[expose] def unadmittedError : Environment := initial 3 ⟨#[7,8]⟩ errorsScript []

@[expose] def raw (success poisoned : Bool) : Environment := {
  nativeRefCounter := 7
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  nativeHeap := [
    (7, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (6, NativeResourceArc.termType shared_log.LogResource,
      .tuple #[.nativeReference 3, .nativeReference 5]),
    (5, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (3, NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 2, NativeCodec.encode NifProperties.payload]),
    (1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode (⟨2⟩ : NativeFile)]),
    (2, NativeFile.typeName, NativeFile.encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0,
      action "write" success (if success then 1 else 4) ⟨#[0]⟩ .nil⟩),
    (4, NativeIoError.typeName, .atom "live")] }

@[expose] def retained (success poisoned resume : Bool)
    (config : Concurrent.Config (core.result.Result (Option U64) U8)) : Bool :=
  let returned := match config.outcome with
    | .ok (.Ok none) => !resume
    | .ok (.Ok (some count)) => resume && success && count.val == 1
    | .ok (.Err error) => resume && !success && error.val == 1
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  returned && env.nativeRefCounter == 8 &&
    (env.nativeHeap.filter (fun cell => cell.1 == 1) == [(1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode (⟨2⟩ : NativeFile)])]) &&
    (env.nativeHeap.filter (fun cell => cell.1 == 3) == [(3,
      NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 1, NativeCodec.encode NifProperties.payload])]) &&
    !(env.nativeHeap.any (fun cell => cell.1 == 7)) &&
    (env.nativeHeap.any (fun cell => cell.1 == 4) == success) &&
    match NativeFile.lookup ⟨2⟩ env with
    | some file => file.visible.data == (if success then #[7] else #[1]) &&
      file.durable.data == #[1] && file.position == (if success then 1 else 0)
    | none => false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 12000000 in
theorem write_outcomes (success poisoned resume : Bool) :
    Concurrent.checkPost (retained success poisoned resume) 512
      (.start (raw success poisoned) (__WRITE__ ⟨3,7⟩ 7#u8 8#u8 resume)) = true := by
  set_option cbv.maxSteps 24000000 in
  cases success <;> cases poisoned <;> cases resume <;> cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 4000000 in
/-- A missing admission does not become a normal Rust result or a catchable
native panic. This is a verification-boundary check, not a native success claim. -/
theorem missing_error_cutoff (resume : Bool) :
    Concurrent.checkPost (fun config => match config.outcome with
      | .error .exhausted => true
      | _ => false) 512
      (.start {raw false false with
        nativeHeap := (raw false false).nativeHeap.filter (fun cell => cell.1 != 4)}
        (__WRITE__ ⟨3,7⟩ 7#u8 8#u8 resume)) = true := by
  cases resume <;> cbv

end LockedAwait.IoNif
