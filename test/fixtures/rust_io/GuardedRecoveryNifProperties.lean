module
public import GuardedRecovery.Properties
public import GuardedRecovery.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.NifProperties
open GuardedRecovery.Properties

theorem recover_contract : __RECOVER__ = io_protocol.reopen_words (toStr "journal") := rfl

@[expose] def facadeRecovered (complete : Bool)
    (config : Concurrent.Config (core.result.Result (Option U16 × Option U16) U8)) : Bool :=
  let returned := match config.outcome with
    | .ok (.Ok (some first,some second)) => complete && first.val == 2055 && second.val == 2569
    | .ok (.Ok (none,none)) => !complete
    | _ => false
  let env := match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
  returned && (Concurrent.nativeEnvironment env).identical
    (Concurrent.nativeEnvironment (Properties.afterAt 12 complete))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem recover_facade_at_restart (complete : Bool) :
    NativeFile.restartFilesystem (Properties.imageAt 12 complete) (Properties.opening complete) =
      some (Properties.bootAt 12 complete) ∧
    Concurrent.checkPost (facadeRecovered complete) 1024
      (.start (Properties.bootAt 12 complete) __RECOVER__) = true := by
  cases complete <;> constructor <;> cbv

@[expose] def writerScript (failed : Bool) : Term :=
  action "write" 2 false (action "write" 2 false
    (.cons (.tuple #[.atom "sync_all",.atom (if failed then "error" else "ok"),
      .integer (if failed then 2 else 0),.bitstring (mask false) 0]) .nil))
@[expose] def initial (failed : Bool) : Environment := {
  nativeRefCounter := 2
  nativeHeap := [
    (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],
      .cons (.tuple #[.atom "open",.bitstring fileName 0,.atom "ok",.integer 0,
        writerScript failed]) .nil⟩),
    (1,NativeFile.inodeTypeName,NativeFile.encode ⟨bytes false,bytes false,0,.nil⟩)] ++
    (if failed then [(2,NativeIoError.typeName,.atom "live")] else []) }
@[expose] def payload : shared_log.LogResource := ⟨⟨4⟩⟩
@[expose] def registered : List String := [NativeResourceArc.typeName shared_log.LogResource]
@[expose] def written (failed : Bool) : Environment := {
  nativeRefCounter := 12
  nativeResourceTypes := registered
  nativeHeap := [
    (8,NativeResourceArc.termType shared_log.LogResource,.tuple #[.nativeReference 5,.nativeReference 7]),
    (7,NativeResourceArc.handleType shared_log.LogResource,.nativeReference 5),
    (5,NativeResourceArc.typeName shared_log.LogResource,.tuple #[.integer 1,NativeCodec.encode payload]),
    (4,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",.atom "unpoisoned",
      NativeCodec.encode (⟨3⟩ : NativeFile)]),
    (3,NativeFile.writableHandleTypeName,NativeFile.encodeHandle ⟨1,4,.nil⟩),
    (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],.nil⟩),
    (1,NativeFile.inodeTypeName,NativeFile.encode ⟨bytes true,bytes (!failed),0,.nil⟩)] }

@[expose] def encodedWords (complete : Bool) : Term :=
  .tuple #[.atom "ok",.tuple #[if complete then .integer 2055 else .atom "nil",
    if complete then .integer 2569 else .atom "nil"]]
@[expose] def recoveredState (complete : Bool) : Environment :=
  {afterAt 12 complete with nativeResourceTypes := registered}

@[expose] def writerInitial : Environment := initial false
@[expose] def completeBoot : Environment := bootAt 12 true
@[expose] def truncatedBoot : Environment := bootAt 12 false

@[expose] def denied : Environment := {
  nativeRefCounter := 12
  nativeHeap := [
    (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],
      .cons (.tuple #[.atom "open",.bitstring fileName 0,.atom "error",.integer 2,.nil]) .nil⟩),
    (1,NativeFile.inodeTypeName,NativeFile.encode ⟨bytes false,bytes false,0,.nil⟩),
    (2,NativeIoError.typeName,.atom "live")] }
@[expose] def deniedAfter : Environment := {
  nativeRefCounter := 12
  nativeResourceTypes := registered
  nativeHeap := [
    (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],.nil⟩),
    (1,NativeFile.inodeTypeName,NativeFile.encode ⟨bytes false,bytes false,0,.nil⟩)] }
@[expose] def unadmitted : Environment := {denied with
  nativeHeap := denied.nativeHeap.filter (fun cell => cell.1 != 2)}

end GuardedRecovery.NifProperties
