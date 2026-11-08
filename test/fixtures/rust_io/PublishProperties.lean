module
public import Publish.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.Properties
open NativeFile

@[expose] def source : Str := Slice.from [97#u8] (by scalar_tac)
@[expose] def target : Str := Slice.from [98#u8] (by scalar_tac)
@[expose] def a : ByteArray := ⟨#[97]⟩
@[expose] def b : ByteArray := ⟨#[98]⟩
@[expose] def content : ByteArray := ⟨#[7,0]⟩
@[expose] def oldNames : Names := [(a,1)]
@[expose] def newNames : Names := [(b,1)]
@[expose] def actionOk (operation : String) (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer 0,.bitstring mask 0]) rest
@[expose] def dirScript : Term := actionOk "sync_dir" ByteArray.empty
  (actionOk "close_dir" ByteArray.empty .nil)
@[expose] def opening : Term :=
  .cons (.tuple #[.atom "open",.bitstring ⟨#[46]⟩ 0,.atom "ok",.integer 0,dirScript]) .nil
@[expose] def renameScript : Term :=
  .cons (.tuple #[.atom "rename",.bitstring a 0,.bitstring b 0,.atom "ok",.integer 0,
    .atom "apply"]) opening
@[expose] def initial : Environment :=
  {nativeRefCounter := 2,nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,actionOk "sync_all" ByteArray.empty
      (actionOk "close" ⟨#[0,0]⟩ .nil)⟩),
    (1,inodeTypeName,encode ⟨content,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}
@[expose] def published : Environment :=
  {nativeRefCounter := 3,nativeHeap := [
    (3,closedDirectoryTypeName,.tuple #[.nil]),
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩)]}

theorem source_bytes : bytes source = a := by
  simp [bytes,source,Slice.from,Slice.val,a,Data.ListN.ListN.from_to_inverse]
theorem target_bytes : bytes target = b := by
  simp [bytes,target,Slice.from,Slice.val,b,Data.ListN.ListN.from_to_inverse]
theorem different : a.data ≠ b.data := by decide +kernel

theorem valid_a : supportedPath a = true := by decide +kernel
theorem valid_b : supportedPath b = true := by decide +kernel
theorem content_size : content.size = 2 := rfl
theorem stable_content : persist content content ⟨#[0,0]⟩ = some content := by decide +kernel

@[expose] def afterSync : Environment :=
  {initial with nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,actionOk "close" ⟨#[0,0]⟩ .nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}
@[expose] def afterClose : Environment :=
  {afterSync with nativeHeap := [
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}
@[expose] def afterRename : Environment :=
  {afterClose with nativeHeap := [
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,oldNames,[newNames],opening⟩)]}
@[expose] def afterOpen : Environment :=
  {nativeRefCounter := 3,nativeHeap := [
    (3,directoryTypeName,.tuple #[dirScript]),
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,oldNames,[newNames],.nil⟩)]}
@[expose] def afterDirectorySync : Environment :=
  {nativeRefCounter := 3,nativeHeap := [
    (3,directoryTypeName,.tuple #[actionOk "close_dir" ByteArray.empty .nil]),
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩)]}

theorem directory_bytes : bytes (toStr ".") = (⟨#[46]⟩ : ByteArray) := by
  simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse]
  exact ⟨46, by decide +kernel, by decide +kernel⟩

theorem sync_poll : pollSync ⟨2⟩ initial = some (.ok (.Ok ()),afterSync) := by
  simp [pollSync,initial,afterSync,renameScript,opening,dirScript,
    actionOk,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,
    inode,decode,encode,limit,syncStep,action,
    blocked,store,sharedStore,encodeNamespace,encodeNames,oldNames,
    content_size,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem close_poll : pollClose ⟨2⟩ afterSync = some (.ok (),afterClose) := by
  simp [pollClose,initial,afterSync,afterClose,renameScript,opening,
    dirScript,actionOk,lookup,sharedLookup,getHandle,decodeHandle,
    encodeHandle,inode,decode,encode,limit,closeStep,
    action,blocked,sharedStore,retire,encodeNamespace,encodeNames,
    oldNames,content_size,stable_content,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem rename_poll : pollRename source target afterClose = some (.ok (.Ok ()),afterRename) := by
  simp [pollRename,initial,afterSync,afterClose,afterRename,renameScript,
    opening,dirScript,actionOk,source_bytes,target_bytes,encodeHandle,
    inode,decode,encode,limit,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    oldNames,newNames,different,valid_a,valid_b,content_size,
    renameChoice,renamedNames,storeNamespace,writableHandleTypeName,closedHandleTypeName,inodeTypeName,
    namespaceTypeName]

theorem open_poll : pollOpenReadOnly (toStr ".") afterRename = some (.ok (.Ok ⟨3⟩),afterOpen) := by
  simp [pollOpenReadOnly,initial,afterSync,afterClose,afterRename,afterOpen,
    renameScript,opening,dirScript,actionOk,directory_bytes,encodeHandle,
    encode,namespaceSnapshot,namespaceState,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    valid_a,valid_b,supportedOpenPath,openChoice,pathChoice,replaceNamespaceScript,
    writableHandleTypeName,closedHandleTypeName,inodeTypeName,namespaceTypeName,directoryTypeName]

theorem directory_sync_poll : pollSync ⟨3⟩ afterOpen = some (.ok (.Ok ()),afterDirectorySync) := by
  simp [pollSync,pollDirectorySync,afterOpen,afterDirectorySync,dirScript,actionOk,
    lookup,encodeHandle,encode,action,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    oldNames,newNames,valid_a,valid_b,storeNamespace,directoryHandle,
    storeDirectory,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,inodeTypeName,
    namespaceTypeName,directoryTypeName]

theorem directory_close_poll : pollClose ⟨3⟩ afterDirectorySync = some (.ok (),published) := by
  simp [pollClose,pollDirectoryClose,published,afterDirectorySync,actionOk,lookup,
    encodeHandle,encode,action,encodeNamespace,encodeNames,newNames,
    directoryHandle,storeDirectory,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

/-- Actual Rust synchronizes data, closes, renames and synchronizes the directory. -/
theorem publish_contract : publish_file ⟨2⟩ source target initial = (.ok (.Ok ()),published) := by
  simp only [publish_file,synchronize_then_close,sync_directory,io_core.synchronize,
    io_core.rename_file,io_core.open_readonly,monadLift_self,NativeOwnedDrop.drop,
    syncAll,close,NativeFile.rename,openReadOnly,Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ sync_poll]
  simp only [Result.ok_bind,Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ close_poll]
  simp only [Result.ok_bind,NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ rename_poll]
  simp only [Result.ok_bind,NativeM.fromRust_ok]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ open_poll]
  simp only [Result.ok_bind,NativeM.fromRust_ok]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ directory_sync_poll]
  simp only [Result.ok_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ directory_close_poll]
  simp []

theorem persist_same (bytes mask result : ByteArray)
    (accepted : persist bytes bytes mask = some result) : result = bytes := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    have size : mask.size = bytes.size := by omega
    cases accepted
    apply ByteArray.ext
    apply _root_.Array.ext
    · simp [size]
    · intro index validMask validBytes
      have bounded : index < bytes.size := by simpa only [ByteArray.size_data] using validBytes
      simp [getElem!_pos, bounded]
      rfl
  · contradiction

/-- Every permitted post-sync byte mask gives the same saved data. -/
theorem checkpoint_image_all (mask result : ByteArray)
    (accepted : persist content content mask = some result) :
    filesystemCrashImage newNames [(1,mask)] published =
      some ⟨newNames,[(1,content)],3⟩ := by
  have same := persist_same content mask result accepted
  subst result
  simp [filesystemCrashImage,published,namespaceSnapshot,namespaceTable,namespaceHistory,
    namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,newNames,valid_b,content_size,inode,decode,encode,
    encodeHandle,limit,accepted,inodeTypeName,namespaceTypeName,closedDirectoryTypeName,
    closedHandleTypeName]

/-- A synchronized directory cannot lose its acknowledged destination name. -/
theorem checkpoint_choice (chosen : Names)
    (accepted : namespaceCrashAllowed ⟨newNames,newNames,[],.nil⟩ chosen = true) :
    namedInode chosen b = some 1 := by
  simp [namespaceCrashAllowed,newNames,namedInode] at accepted
  obtain ⟨path,found⟩ := accepted.2
  simp [namedInode,found]

/-- Neither process capabilities nor the unsynchronized old byte image survive restart. -/
theorem checkpoint_image :
    filesystemCrashImage newNames [(1,⟨#[0,0]⟩)] published =
      some ⟨newNames,[(1,content)],3⟩ := by
  simp [filesystemCrashImage,published,namespaceSnapshot,namespaceTable,namespaceHistory,
    namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,namespaceCrashAllowed,namedInode,
    newNames,valid_b,content_size,inode,decode,encode,encodeHandle,limit,stable_content,
    inodeTypeName,namespaceTypeName,closedDirectoryTypeName,closedHandleTypeName]

@[expose] def reopening : Term :=
  .cons (.tuple #[.atom "open",.bitstring b 0,.atom "ok",.integer 0,.nil]) .nil
@[expose] def rebooted : Environment :=
  {nativeRefCounter := 3,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],reopening⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩)]}
@[expose] def recovered : Environment :=
  {nativeRefCounter := 4,nativeHeap := [
    (4,handleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩)]}

theorem restart_checkpoint :
    restartFilesystem ⟨newNames,[(1,content)],3⟩ reopening = some rebooted := by rfl

set_option maxRecDepth 4096 in
/-- The extracted cross-crate opener resolves the durable name to the saved inode. -/
theorem recover_published : open_readonly target rebooted = (.ok (.Ok ⟨4⟩),recovered) := by
  have poll : pollOpenReadOnly target rebooted = some (.ok (.Ok ⟨4⟩),recovered) := by
    simp [pollOpenReadOnly,target_bytes,
      supportedOpenPath,valid_b,rebooted,recovered,reopening,newNames,content_size,
      namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,decode,encode,
      limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,handleTypeName]
    decide +kernel
  simp only [open_readonly,io_core.open_readonly,monadLift_self,openReadOnly]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp

/-- Publication is composed with restart and the actual Rust opener. Every
accepted post-acknowledgment tearing mask preserves the saved contents. -/
theorem publication_restart (mask result : ByteArray)
    (accepted : persist content content mask = some result) :
    publish_file ⟨2⟩ source target initial = (.ok (.Ok ()),published) ∧
    filesystemCrashImage newNames [(1,mask)] published = some ⟨newNames,[(1,content)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,content)],3⟩ reopening = some rebooted ∧
    open_readonly target rebooted = (.ok (.Ok ⟨4⟩),recovered) ∧
    (lookup ⟨4⟩ recovered).map (·.visible) = some content := by
  refine ⟨publish_contract,checkpoint_image_all mask result accepted,
    restart_checkpoint,recover_published,?_⟩
  simp [lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,recovered,inode,decode,
    encode,limit,content_size,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]

/-- Unsynchronized rename metadata can be lost or persist only partially.
The model makes no success claim for a caller interrupted before acknowledgment. -/
theorem pending_choices :
    namespaceCrashAllowed ⟨newNames,oldNames,[newNames],.nil⟩ [] = true ∧
    namespaceCrashAllowed ⟨newNames,oldNames,[newNames],.nil⟩ (oldNames ++ newNames) = true ∧
    namespaceCrashAllowed ⟨newNames,newNames,[],.nil⟩ [] = false := by
  decide +kernel

/-- Admission rejects fabricated metadata and incomplete inode choices. -/
theorem invalid_crash_choices :
    (filesystemCrashImage [(a,1)] [(1,⟨#[0,0]⟩)] published).isNone = true ∧
    (filesystemCrashImage newNames [] published).isNone = true ∧
    (filesystemCrashImage newNames [(1,⟨#[0,0]⟩),(1,⟨#[0,0]⟩)] published).isNone = true ∧
    (restartFilesystem ⟨newNames,[],3⟩ .nil).isNone = true ∧
    (restartFilesystem ⟨newNames,[(1,content),(1,content)],3⟩ .nil).isNone = true ∧
    (restartFilesystem ⟨newNames,[(1,content)],0⟩ .nil).isNone = true := by
  decide +kernel

theorem old_capabilities_gone :
    lookup ⟨2⟩ rebooted = none ∧ directoryHandle ⟨3⟩ rebooted = none := by
  simp [lookup,sharedLookup,getHandle,directoryHandle,rebooted,namespaceTypeName,
    inodeTypeName,typeName,handleTypeName,writableHandleTypeName]

end Publish.Properties
