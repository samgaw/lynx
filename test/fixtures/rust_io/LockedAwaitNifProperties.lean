module
public import Lynx
public import LockedAwait.Properties
public import LockedAwait.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace LockedAwait.NifProperties

theorem open_contract : __OPEN__ = (do
    let opened ← io_protocol.open_readwrite (toStr "journal")
    match opened with
    | .Ok file => do
      let mutex ← NativeMutex.new file
      let owner ← NativeResourceArc.newOwned ({file := mutex} : shared_log.LogResource)
      NativeM.ok (.Ok owner)
    | .Err error => do
      NativeIoError.dispose error
      NativeM.ok (.Err (Rustler.atomErrorOutcome "open_failed"))) := by
  simp [__OPEN__,
    NativeOwnedDrop.drop, NativeM.ok, LockedAwait.Extraction.ErrorConstants.literal_0]
  rfl

theorem write_contract (owner : NativeResourceArc shared_log.LogResource)
    (first second : U8) (resume : Bool) :
    __WRITE__ owner first second resume = (do
      let payload ← NativeResourceArc.deref owner
      let result ← io_protocol.poll_locked_write payload.file (Array.make 2#usize [first, second]) resume
      NativeResourceArc.releaseOwned owner
      match result with
      | none => NativeM.ok (.Ok none)
      | some (.Err error) => NativeM.ok (.Err error)
      | some (.Ok count) => NativeM.ok (.Ok (some (UScalar.cast .U64 count)))) := by
  simp [__WRITE__,
    NativeOwnedDrop.drop, NativeM.ok, NativeM.lift]
  congr 1
  funext payload
  congr 1
  funext result
  cases result with
  | none => rfl
  | some reply => cases reply <;> rfl

@[expose] def outcome (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom "write", .atom "ok", .integer count, .bitstring ⟨#[0]⟩ 0]) rest
@[expose] def payload : shared_log.LogResource := ⟨⟨1⟩⟩
@[expose] def initial (poisoned : Bool) : Environment := {
  nativeRefCounter := 8
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  nativeHeap := [
    (8, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (7, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (6, NativeResourceArc.termType shared_log.LogResource, .tuple #[.nativeReference 3, .nativeReference 5]),
    (5, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (3, NativeResourceArc.typeName shared_log.LogResource, .tuple #[.integer 3, NativeCodec.encode payload]),
    (1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode (⟨2⟩ : NativeFile)]),
    (2, NativeFile.typeName, NativeFile.encode
      ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, outcome 2 (outcome 2 .nil)⟩)] }

@[expose] def retained (poisoned : Bool)
    (config : Concurrent.Config (core.result.Result (Option U64) U8 × core.result.Result (Option U64) U8)) : Bool :=
  let returned := match config.outcome with
    | .ok (.Ok none, .Ok (some count)) => count.val == 2
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  returned && env.nativeRefCounter == 10 &&
    (env.nativeHeap.filter (fun cell => cell.1 == 1) == [(1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode (⟨2⟩ : NativeFile)])]) &&
    (env.nativeHeap.filter (fun cell => cell.1 == 3) == [(3,
      NativeResourceArc.typeName shared_log.LogResource, .tuple #[.integer 1, NativeCodec.encode payload])]) &&
    !(env.nativeHeap.any (fun cell => cell.1 == 7 || cell.1 == 8)) &&
    match NativeFile.lookup ⟨2⟩ env with
    | some file => file.visible.data == #[7,8,9,10] && file.durable.data == #[1] && file.position == 4
    | none => false

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem shared_cancel_resume (poisoned : Bool) :
    Concurrent.checkPost (retained poisoned) 512 (.start (initial poisoned) (do
      let first ← __WRITE__ ⟨3,7⟩ 7#u8 8#u8 false
      let second ← __WRITE__ ⟨3,8⟩ 9#u8 10#u8 true
      NativeM.ok (first, second))) = true := by
  set_option cbv.maxSteps 12000000 in cases poisoned <;> cbv


@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : NativeFile.Names := [(fileName, 1)]
@[expose] def action (operation : String) (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom "ok", .integer count, .bitstring ⟨#[0]⟩ 0]) rest
@[expose] def script : Term :=
  action "write" 2 (action "write" 2
    (action "seek" 0 (action "read" 1 (action "read" 1
      (action "seek" 0 (action "read" 1 (action "read" 1 .nil)))))))
@[expose] def namedInitial : Environment := {
  nativeRefCounter := 1
  nativeHeap := [
    (0, NativeFile.namespaceTypeName, NativeFile.encodeNamespace ⟨names, names, [],
      .cons (.tuple #[.atom "open", .bitstring fileName 0, .atom "ok", .integer 0, script]) .nil⟩),
    (1, NativeFile.inodeTypeName, NativeFile.encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, .nil⟩)] }
@[expose] def rejected : Environment := {
  nativeRefCounter := 2
  nativeHeap := [
    (0, NativeFile.namespaceTypeName, NativeFile.encodeNamespace ⟨[], [], [],
      .cons (.tuple #[.atom "open", .bitstring fileName 0, .atom "error", .integer 2, .nil]) .nil⟩),
    (2, NativeIoError.typeName, .atom "live")] }

end LockedAwait.NifProperties
