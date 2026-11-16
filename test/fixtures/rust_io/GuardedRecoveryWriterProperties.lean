module
public import GuardedRecovery.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace GuardedRecovery.Writer
open GuardedRecovery.Properties

@[expose] def mutex : Term := .tuple #[.atom "unlocked",.atom "unpoisoned",
  NativeCodec.encode (⟨2⟩ : NativeFile)]
@[expose] def fileCells (durable : ByteArray) (position : Nat) (script : Term) :
    List (Nat × String × Term) := [
  (4,NativeMutex.typeName NativeFile,mutex),
  (2,NativeFile.writableHandleTypeName,NativeFile.encodeHandle ⟨1,position,script⟩),
  (0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],.nil⟩),
  (1,NativeFile.inodeTypeName,NativeFile.encode ⟨bytes true,durable,0,.nil⟩)]
@[expose] def errorAction (failed : Bool) : Term :=
  .cons (.tuple #[.atom "sync_all",.atom (if failed then "error" else "ok"),
    .integer (if failed then 3 else 0),.bitstring (mask false) 0]) .nil
@[expose] def writerScript (failed : Bool) : Term :=
  action "write" 2 false (action "write" 2 false (errorAction failed))
@[expose] def before (failed : Bool) : Environment := {
  nativeRefCounter := 4
  nativeHeap := (fileCells (bytes false) 0 (writerScript failed)).map (fun cell =>
    if cell.1 == 1 then (1,NativeFile.inodeTypeName,
      NativeFile.encode ⟨bytes false,bytes false,0,.nil⟩) else cell) ++
    (if failed then [(3,NativeIoError.typeName,.atom "live")] else []) }
@[expose] def written (failed : Bool) : Environment := {
  nativeRefCounter := 6
  nativeHeap := fileCells (bytes (!failed)) 4 .nil }
@[expose] def snapshot (config : Concurrent.Config α) : Environment :=
  match config with | .start env .. => env | .running runtime .. => runtime.nativeView []
@[expose] def accepted (failed : Bool)
    (config : Concurrent.Config
      (Option (core.result.Result Usize U8) × Option (core.result.Result Usize U8))) : Bool :=
  let returned := match config.outcome with
    | .ok (none,some (.Ok count)) => !failed && count.val == 2
    | .ok (none,some (.Err code)) => failed && code.val == 2
    | _ => false
  let env := snapshot config
  returned && (Concurrent.nativeEnvironment env).identical
    (Concurrent.nativeEnvironment (written failed))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem writer_transitions (failed : Bool) :
    Concurrent.checkPost (accepted failed) 1024 (.start (before failed) (do
      let cancelled ← poll_locked_sync ⟨4⟩ (Array.make 2#usize [7#u8,8#u8]) false
      let resumed ← poll_locked_sync ⟨4⟩ (Array.make 2#usize [9#u8,10#u8]) true
      NativeM.ok (cancelled,resumed))) = true := by
  set_option cbv.maxSteps 24000000 in
  cases failed <;> cbv

set_option maxHeartbeats 8000000 in
theorem acknowledged_image (choice saved : ByteArray)
    (admitted : NativeFile.persist (bytes true) (bytes true) choice = some saved) :
    NativeFile.filesystemCrashImage names [(1,choice)] (written false) = some (image true) := by
  have same := NativeFile.persist_same (bytes true) choice saved admitted
  subst saved
  have path : NativeFile.supportedPath fileName = true := by decide +kernel
  have size : (bytes true).size = 4 := rfl
  simp only [bytes, ↓reduceIte] at size
  simp only [fileName] at path
  simp only [bytes, ↓reduceIte] at admitted
  simp [path,size,NativeFile.filesystemCrashImage,written,fileCells,NativeFile.namespaceSnapshot,
    NativeFile.namespaceTable,NativeFile.namespaceHistory,NativeFile.namespaceEntry,
    NativeFile.encodeNamespace,NativeFile.encodeNames,NativeFile.tablesEqual,List.eraseDups_cons,
    NativeFile.namespaceCrashAllowed,NativeFile.namedInode,names,fileName,bytes,image,
    NativeFile.inode,NativeFile.decode,NativeFile.encode,NativeFile.limit,admitted,
    NativeFile.inodeTypeName,NativeFile.namespaceTypeName,NativeFile.writableHandleTypeName,
    NativeMutex.typeName,NativeCodec.typeName,mutex]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
theorem failed_sync_can_lose_writes :
    NativeFile.filesystemCrashImage names [(1,mask false)] (written true) = some (image false) ∧
    Concurrent.checkPost (recovered false) 1024
      (.start (boot false) (reopen_words (toStr "journal"))) = true := by
  constructor
  · cbv
  · exact (recovery_after_restart false).2

/-- Any admitted post-acknowledgement byte choice composes with actual reopened
Rust recovery. Neither the old mutex nor its file handle survives restart. -/
theorem acknowledged_recovery (choice saved : ByteArray)
    (admitted : NativeFile.persist (bytes true) (bytes true) choice = some saved) :
    NativeFile.filesystemCrashImage names [(1,choice)] (written false) = some (image true) ∧
    NativeFile.restartFilesystem (image true) (opening true) = some (boot true) ∧
    Concurrent.checkPost (recovered true) 1024
      (.start (boot true) (reopen_words (toStr "journal"))) = true :=
  ⟨acknowledged_image choice saved admitted, recovery_after_restart true⟩

/-- The checker postcondition fixes every file-model input used at power loss. -/
theorem accepted_state (config : Concurrent.Config
      (Option (core.result.Result Usize U8) × Option (core.result.Result Usize U8)))
    (checked : accepted false config = true) :
    (snapshot config).nativeRefCounter = (written false).nativeRefCounter ∧
    (snapshot config).nativeHeap = (written false).nativeHeap := by
  simp only [accepted, Bool.and_eq_true] at checked
  have equal := Concurrent.NativeState.eq_of_identical checked.2
  exact ⟨congrArg Concurrent.NativeState.refCounter equal,
    congrArg Concurrent.NativeState.heap equal⟩

/-- Compose all terminal runs of the actual two-call writer with every admitted
post-sync byte image and the actual fresh Rust recovery implementation. -/
theorem every_acknowledged_recovery (choice saved : ByteArray)
    (admitted : NativeFile.persist (bytes true) (bytes true) choice = some saved)
    (run : Concurrent.Run (.start (before false) (do
      let cancelled ← poll_locked_sync ⟨4⟩ (Array.make 2#usize [7#u8,8#u8]) false
      let resumed ← poll_locked_sync ⟨4⟩ (Array.make 2#usize [9#u8,10#u8]) true
      NativeM.ok (cancelled,resumed))) events last)
    (terminal : Concurrent.Terminal last outcome) :
    NativeFile.filesystemCrashImage names [(1,choice)] (snapshot last) = some (image true) ∧
    NativeFile.restartFilesystem (image true) (opening true) = some (boot true) ∧
    Concurrent.checkPost (recovered true) 1024
      (.start (boot true) (reopen_words (toStr "journal"))) = true := by
  have checked := Concurrent.checkPost_sound (writer_transitions false) run terminal
  obtain ⟨counter,heap⟩ := accepted_state last checked
  refine ⟨?_,recovery_after_restart true⟩
  simpa only [NativeFile.filesystemCrashImage, NativeFile.namespaceSnapshot, NativeFile.inode,
    counter,heap] using acknowledged_image choice saved admitted

end GuardedRecovery.Writer
