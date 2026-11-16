module
__EXTERNAL_IMPORTS__
public import GuardedRecovery.NifProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.AdapterProof
open GuardedRecovery.Properties GuardedRecovery.NifProperties

@[expose] def dispatcher : Dispatcher := Dispatcher.ofTable [] 0
@[expose] def writer : Result (Term × Term) := do
  let owner ← __NAMESPACE__.«async_log_open/0» dispatcher
  let cancelled ← __NAMESPACE__.«async_log_sync/4» dispatcher owner (.integer 7) (.integer 8) Term.false
  let resumed ← __NAMESPACE__.«async_log_sync/4» dispatcher owner (.integer 9) (.integer 10) Term.true
  return (cancelled,resumed)
@[expose] def recovery : Result Term := __NAMESPACE__.«async_log_recover/0» dispatcher
@[expose] def snapshot (config : Concurrent.Config α) : Environment :=
  match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
@[expose] def writerAccepted (failed : Bool) (config : Concurrent.Config (Term × Term)) : Bool :=
  let returned := match config.outcome with
    | .ok (cancelled,resumed) =>
      cancelled.identical (.tuple #[.atom "ok",.atom "nil"]) &&
      resumed.identical (.tuple #[.atom (if failed then "error" else "ok"),.integer 2])
    | _ => false
  returned && (Concurrent.nativeEnvironment (snapshot config)).identical
    (Concurrent.nativeEnvironment (written failed))
@[expose] def recoveryAccepted (complete : Bool) (config : Concurrent.Config Term) : Bool :=
  let returned := match config.outcome with
    | .ok result => result.identical (encodedWords complete)
    | _ => false
  returned && (Concurrent.nativeEnvironment (snapshot config)).identical
    (Concurrent.nativeEnvironment (recoveredState complete))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem writer_checked (failed : Bool) :
    Concurrent.checkPost (writerAccepted failed) 1024 (.start (initial failed) writer) = true := by
  set_option cbv.maxSteps 32000000 in
  cases failed <;> cbv

set_option maxRecDepth 16384 in
set_option maxHeartbeats 16000000 in
theorem recovery_checked (complete : Bool) :
    NativeFile.restartFilesystem (imageAt 12 complete) (opening complete) = some (bootAt 12 complete) ∧
    Concurrent.checkPost (recoveryAccepted complete) 1024
      (.start (bootAt 12 complete) recovery) = true := by
  set_option cbv.maxSteps 32000000 in
  cases complete <;> constructor <;> cbv

theorem accepted_state (config : Concurrent.Config (Term × Term))
    (accepted : writerAccepted false config = true) :
    (snapshot config).nativeRefCounter = (written false).nativeRefCounter ∧
    (snapshot config).nativeHeap = (written false).nativeHeap := by
  simp only [writerAccepted, Bool.and_eq_true] at accepted
  have equal := Concurrent.NativeState.eq_of_identical accepted.2
  exact ⟨congrArg Concurrent.NativeState.refCounter equal,congrArg Concurrent.NativeState.heap equal⟩

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem acknowledged_image (choice saved : ByteArray)
    (admitted : NativeFile.persist (bytes true) (bytes true) choice = some saved) :
    NativeFile.filesystemCrashImage names [(1,choice)] (written false) = some (imageAt 12 true) := by
  have same := NativeFile.persist_same (bytes true) choice saved admitted
  subst saved
  have path : NativeFile.supportedPath fileName = true := by decide +kernel
  have size : (bytes true).size = 4 := rfl
  simp only [fileName] at path
  simp only [bytes, ↓reduceIte] at size admitted
  simp [path,size,NativeFile.filesystemCrashImage,written,registered,payload,
    NativeFile.namespaceSnapshot,NativeFile.namespaceTable,NativeFile.namespaceHistory,
    NativeFile.namespaceEntry,NativeFile.encodeNamespace,NativeFile.encodeNames,
    NativeFile.tablesEqual,List.eraseDups_cons,NativeFile.namespaceCrashAllowed,
    NativeFile.namedInode,names,fileName,bytes,imageAt,NativeFile.inode,NativeFile.decode,
    NativeFile.encode,NativeFile.limit,admitted,NativeFile.inodeTypeName,NativeFile.namespaceTypeName,
    NativeFile.writableHandleTypeName,NativeResourceArc.typeName,NativeResourceArc.termType,
    NativeResourceArc.handleType,NativeMutex.typeName,NativeCodec.typeName]

/-- The actual generated Rustler adapters compose through every terminal writer
run, every admitted post-ack data mask, and fresh decoded/encoded recovery. -/
theorem every_adapter_recovery (choice saved : ByteArray)
    (admitted : NativeFile.persist (bytes true) (bytes true) choice = some saved)
    (run : Concurrent.Run (.start (initial false) writer) events last)
    (terminal : Concurrent.Terminal last outcome) :
    NativeFile.filesystemCrashImage names [(1,choice)] (snapshot last) = some (imageAt 12 true) ∧
    NativeFile.restartFilesystem (imageAt 12 true) (opening true) = some (bootAt 12 true) ∧
    ∀ recoveryEvents recoveryLast recoveryOutcome,
      Concurrent.Run (.start (bootAt 12 true) recovery) recoveryEvents recoveryLast →
      Concurrent.Terminal recoveryLast recoveryOutcome → recoveryAccepted true recoveryLast = true := by
  have checked := Concurrent.checkPost_sound (writer_checked false) run terminal
  obtain ⟨counter,heap⟩ := accepted_state last checked
  refine ⟨?_,(recovery_checked true).1,?_⟩
  · simpa only [NativeFile.filesystemCrashImage,NativeFile.namespaceSnapshot,NativeFile.inode,
      counter,heap] using acknowledged_image choice saved admitted
  · intro _ _ _ recovered terminal
    exact Concurrent.checkPost_sound (recovery_checked true).2 recovered terminal

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem failed_sync_loss :
    NativeFile.filesystemCrashImage names [(1,mask false)] (written true) = some (imageAt 12 false) ∧
    Concurrent.checkPost (recoveryAccepted false) 1024
      (.start (bootAt 12 false) recovery) = true := by
  constructor
  · cbv
  · exact (recovery_checked false).2

@[expose] def deniedAccepted (config : Concurrent.Config Term) : Bool :=
  let returned := match config.outcome with
    | .ok value => value.identical (.tuple #[.atom "error",.integer 3])
    | _ => false
  returned && (Concurrent.nativeEnvironment (snapshot config)).identical
    (Concurrent.nativeEnvironment deniedAfter)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem opening_error_checked :
    Concurrent.checkPost deniedAccepted 512 (.start denied recovery) = true := by cbv

end GuardedRecovery.AdapterProof

#check GuardedRecovery.AdapterProof.every_adapter_recovery
