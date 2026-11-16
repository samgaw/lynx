module
public import Lynx
public import GuardedSync.NifProperties
public import GuardedSync.Io
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedSync.IoNif

@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def names : NativeFile.Names := [(fileName, 1)]
@[expose] def readWord (mask : ByteArray) (rest : Term) : Term :=
  Io.action "seek" true 0 mask
    (Io.action "read" true 1 mask (Io.action "read" true 1 mask rest))
@[expose] def syncScript (failed : Bool) : Term :=
  let mask : ByteArray := if failed then ⟨#[0]⟩ else ⟨#[0,0,0,0]⟩
  Io.action "write" true 2 ⟨#[0]⟩ (Io.action "write" true 2 ⟨#[0]⟩
    (Io.action "sync_all" (!failed) (if failed then 2 else 0) ⟨#[0]⟩
      (readWord mask (readWord mask .nil))))
@[expose] def initial (failed : Bool) : Environment := {
  nativeRefCounter := if failed then 2 else 1
  nativeHeap := [
    (0, NativeFile.namespaceTypeName, NativeFile.encodeNamespace ⟨names, names, [],
      .cons (.tuple #[.atom "open", .bitstring fileName 0, .atom "ok", .integer 0,
        syncScript failed]) .nil⟩),
    (1, NativeFile.inodeTypeName, NativeFile.encode ⟨⟨#[1]⟩, ⟨#[1]⟩, 0, .nil⟩)] ++
    (if failed then [(2, NativeIoError.typeName, .atom "live")] else []) }
@[expose] def success : Environment := initial false
@[expose] def failure : Environment := initial true
@[expose] def unadmitted : Environment := {failure with
  nativeHeap := failure.nativeHeap.filter (fun cell => cell.1 != 2)}

@[expose] def payload : shared_log.LogResource := ⟨⟨1⟩⟩
@[expose] def resourceState (owning : Bool) (file : NativeFile.State)
    (errors : List Nat) : Environment := {
  nativeRefCounter := if owning then 7 else 8
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  nativeHeap := (if owning then
    [(7, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3)] else []) ++ [
    (6, NativeResourceArc.termType shared_log.LogResource,
      .tuple #[.nativeReference 3, .nativeReference 5]),
    (5, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3),
    (3, NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer (if owning then 2 else 1), NativeCodec.encode payload]),
    (1, NativeMutex.typeName NativeFile, Io.mutex),
    (2, NativeFile.typeName, NativeFile.encode file)] ++
    errors.map (fun id => (id, NativeIoError.typeName, .atom "live")) }
@[expose] def syncChoice (failed persisted : Bool) : Term :=
  Io.action "sync_all" (!failed) (if failed then 4 else 0)
    ⟨#[if persisted then 1 else 0]⟩ .nil
@[expose] def raw (failed persisted short : Bool) : Environment :=
  resourceState true ⟨⟨#[1]⟩, ⟨#[1]⟩, 0,
    Io.action "write" true (if short then 1 else 2) ⟨#[0]⟩ (syncChoice failed persisted)⟩
    (if failed then [4] else [])
@[expose] def expected (resume failed persisted short : Bool) : Environment :=
  resourceState false ⟨Io.visible short,
    if resume then (if failed then (if persisted then ⟨#[7]⟩ else ⟨#[1]⟩) else Io.visible short)
    else ⟨#[1]⟩,
    if short then 1 else 2, if resume then .nil else syncChoice failed persisted⟩
    (if failed && !resume then [4] else [])
@[expose] def retained (resume failed persisted short : Bool)
    (config : Concurrent.Config (core.result.Result (Option U64) U8)) : Bool :=
  let returned := match config.outcome with
    | .ok (.Ok none) => !resume
    | .ok (.Ok (some count)) => resume && !failed && count.val == (if short then 1 else 2)
    | .ok (.Err code) => resume && failed && code.val == 2
    | _ => false
  let env := match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
  returned && env.nativeRefCounter == 8 &&
    env.nativeHeap == (expected resume failed persisted short).nativeHeap

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem sync_outcomes (resume failed persisted short : Bool) :
    Concurrent.checkPost (retained resume failed persisted short) 512
      (.start (raw failed persisted short) (__SYNC__ ⟨3,7⟩ 7#u8 8#u8 resume)) = true := by
  simp only [NifProperties.sync_contract, Properties.caller_contract,
    Properties.synchronize_contract, io_core.write_once, monadLift_self]
  set_option cbv.maxSteps 32000000 in
  cases resume <;> cases failed <;> cases persisted <;> cases short <;> cbv

@[expose] def sharedBefore (failed : Bool) : Environment :=
  let env := resourceState true ⟨⟨#[1]⟩, ⟨#[1]⟩, 0,
    Io.action "write" true 2 ⟨#[0]⟩
      (Io.action "write" true 2 ⟨#[0]⟩ (syncChoice failed false))⟩
    (if failed then [4] else [])
  {env with nativeRefCounter := 8, nativeHeap := (8, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3) ::
      env.nativeHeap.map (fun cell => if cell.1 == 3 then
        (3, NativeResourceArc.typeName shared_log.LogResource,
          .tuple #[.integer 3, NativeCodec.encode payload]) else cell)}
@[expose] def sharedAfter (failed : Bool) : Environment :=
  {resourceState false ⟨⟨#[7,8,9,10]⟩,
    if failed then ⟨#[1]⟩ else ⟨#[7,8,9,10]⟩, 4, .nil⟩ [] with nativeRefCounter := 10}
@[expose] def sharedRetained (failed : Bool)
    (config : Concurrent.Config
      (core.result.Result (Option U64) U8 × core.result.Result (Option U64) U8)) : Bool :=
  let returned := match config.outcome with
    | .ok (.Ok none, .Ok (some count)) => !failed && count.val == 2
    | .ok (.Ok none, .Err code) => failed && code.val == 2
    | _ => false
  let env := match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
  returned && env.nativeRefCounter == 10 && env.nativeHeap == (sharedAfter failed).nativeHeap

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem cancelled_prefix_synchronization (failed : Bool) :
    Concurrent.checkPost (sharedRetained failed) 1024 (.start (sharedBefore failed) (do
      let cancelled ← __SYNC__ ⟨3,7⟩ 7#u8 8#u8 false
      let resumed ← __SYNC__ ⟨3,8⟩ 9#u8 10#u8 true
      NativeM.ok (cancelled, resumed))) = true := by
  set_option cbv.maxSteps 24000000 in
  cases failed <;> cbv

end GuardedSync.IoNif
