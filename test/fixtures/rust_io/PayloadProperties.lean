module
public import Publish.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.Payload
open NativeFile Publish.Properties

@[expose] def zeroMask (data : ByteArray) : ByteArray := ⟨_root_.Array.replicate data.size 0⟩

theorem persist_zero (data : ByteArray) : persist data data (zeroMask data) = some data := by
  have conditions : data.size ≤ (zeroMask data).size ∧
      (zeroMask data).size ≤ data.size ∧
      ((zeroMask data).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [zeroMask, ← ByteArray.size_data]
  let result : ByteArray := ⟨(zeroMask data).data.mapIdx fun index choice =>
    if choice == 1 then data[index]! else data[index]!⟩
  have accepted : persist data data (zeroMask data) = some result := by
    unfold persist
    simp only [Nat.min_self, Nat.max_self]
    rw [if_pos conditions]
  rw [persist_same data (zeroMask data) result accepted] at accepted
  exact accepted

theorem not_directory : (b.data == #[46]) = false := by decide +kernel

variable (data : ByteArray) (bounded : data.size ≤ limit)

@[expose] def initial : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,actionOk "sync_all" ByteArray.empty
      (actionOk "close" (zeroMask data) .nil)⟩),
    (1,inodeTypeName,encode ⟨data,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}
@[expose] def published : Environment :=
  {refCounter := 3,nativeHeap := [
    (3,closedDirectoryTypeName,.tuple #[.nil]),
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩)]}

@[expose] def afterSync : Environment :=
  {(initial data) with nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,actionOk "close" (zeroMask data) .nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}
@[expose] def afterClose : Environment :=
  {(afterSync data) with nativeHeap := [
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}
@[expose] def afterRename : Environment :=
  {(afterClose data) with nativeHeap := [
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,oldNames,[newNames],opening⟩)]}
@[expose] def afterOpen : Environment :=
  {refCounter := 3,nativeHeap := [
    (3,directoryTypeName,.tuple #[dirScript]),
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,oldNames,[newNames],.nil⟩)]}
@[expose] def afterDirectorySync : Environment :=
  {refCounter := 3,nativeHeap := [
    (3,directoryTypeName,.tuple #[actionOk "close_dir" ByteArray.empty .nil]),
    (2,closedHandleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩)]}

include bounded

theorem sync_poll : pollSync ⟨2⟩ (initial data) = some (.ok (.Ok ()),(afterSync data)) := by
  simp only [limit] at bounded
  simp [pollSync,initial,afterSync,renameScript,opening,dirScript,
    actionOk,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,
    inode,decode,encode,limit,syncStep,action,
    blocked,store,sharedStore,encodeNamespace,encodeNames,oldNames,
    not_lt.mpr bounded,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem close_poll : pollClose ⟨2⟩ (afterSync data) = some (.ok (),(afterClose data)) := by
  simp only [limit] at bounded
  simp [pollClose,initial,afterSync,afterClose,renameScript,opening,
    dirScript,actionOk,lookup,sharedLookup,getHandle,decodeHandle,
    encodeHandle,inode,decode,encode,limit,closeStep,
    action,blocked,sharedStore,retire,encodeNamespace,encodeNames,
    oldNames,not_lt.mpr bounded,persist_zero,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem rename_poll : pollRename source target (afterClose data) = some (.ok (.Ok ()),(afterRename data)) := by
  simp only [limit] at bounded
  simp [pollRename,initial,afterSync,afterClose,afterRename,renameScript,
    opening,dirScript,actionOk,source_bytes,target_bytes,encodeHandle,
    inode,decode,encode,limit,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    oldNames,newNames,different,valid_a,valid_b,not_lt.mpr bounded,
    renameChoice,renamedNames,storeNamespace,writableHandleTypeName,closedHandleTypeName,inodeTypeName,
    namespaceTypeName]

theorem open_poll : pollOpenReadOnly (toStr ".") (afterRename data) = some (.ok (.Ok ⟨3⟩),(afterOpen data)) := by
  simp only [limit] at bounded
  simp [pollOpenReadOnly,initial,afterSync,afterClose,afterRename,afterOpen,
    renameScript,opening,dirScript,actionOk,directory_bytes,encodeHandle,
    encode,namespaceSnapshot,namespaceState,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    valid_a,valid_b,supportedOpenPath,openChoice,pathChoice,replaceNamespaceScript,
    writableHandleTypeName,closedHandleTypeName,inodeTypeName,namespaceTypeName,directoryTypeName]

theorem directory_sync_poll : pollSync ⟨3⟩ (afterOpen data) = some (.ok (.Ok ()),(afterDirectorySync data)) := by
  simp only [limit] at bounded
  simp [pollSync,pollDirectorySync,afterOpen,afterDirectorySync,dirScript,actionOk,
    lookup,encodeHandle,encode,action,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    oldNames,newNames,valid_a,valid_b,storeNamespace,directoryHandle,
    storeDirectory,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,inodeTypeName,
    namespaceTypeName,directoryTypeName]

theorem directory_close_poll : pollClose ⟨3⟩ (afterDirectorySync data) = some (.ok (),(published data)) := by
  simp only [limit] at bounded
  simp [pollClose,pollDirectoryClose,published,afterDirectorySync,actionOk,lookup,
    encodeHandle,encode,action,encodeNamespace,encodeNames,newNames,
    directoryHandle,storeDirectory,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

/-- Actual Rust synchronizes data, closes, renames and synchronizes the directory. -/
theorem publish_contract : publish_file ⟨2⟩ source target (initial data) = (.ok (.Ok ()),(published data)) := by
  simp only [limit] at bounded
  simp only [publish_file,synchronize_then_close,sync_directory,io_core.synchronize,
    io_core.rename_file,io_core.open_readonly,monadLift_self,NativeOwnedDrop.drop,
    syncAll,close,NativeFile.rename,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (sync_poll data bounded)]
  simp only [Result.ok_bind,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll data bounded)]
  simp only [Result.ok_bind,NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (rename_poll data bounded)]
  simp only [Result.ok_bind,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll data bounded)]
  simp only [Result.ok_bind,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (directory_sync_poll data bounded)]
  simp only [Result.ok_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (directory_close_poll data bounded)]
  simp []

/-- Every permitted post-sync byte mask gives the same saved data. -/
theorem checkpoint_image_all (mask result : ByteArray)
    (accepted : persist data data mask = some result) :
    filesystemCrashImage newNames [(1,mask)] (published data) =
      some ⟨newNames,[(1,data)],3⟩ := by
  simp only [limit] at bounded
  have same := persist_same data mask result accepted
  subst result
  simp [filesystemCrashImage,published,namespaceSnapshot,namespaceTable,namespaceHistory,
    namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,newNames,valid_b,not_lt.mpr bounded,inode,decode,encode,
    encodeHandle,limit,accepted,inodeTypeName,namespaceTypeName,closedDirectoryTypeName,
    closedHandleTypeName]

@[expose] def rebooted : Environment :=
  {refCounter := 3,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],reopening⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩)]}
@[expose] def recovered : Environment :=
  {refCounter := 4,nativeHeap := [
    (4,handleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩)]}

theorem restart_checkpoint :
    restartFilesystem ⟨newNames,[(1,data)],3⟩ reopening = some (rebooted data) := by
  simp only [limit] at bounded
  simp [restartFilesystem,limit,rebooted,newNames,namespaceTable,namespaceEntry,encodeNames,
    List.eraseDups_cons,valid_b,not_lt.mpr bounded,inodeTypeName,namespaceTypeName]

set_option maxRecDepth 4096 in
/-- The extracted cross-crate opener resolves the durable name to the saved inode. -/
theorem recover_published : open_readonly target (rebooted data) = (.ok (.Ok ⟨4⟩),(recovered data)) := by
  simp only [limit] at bounded
  have poll : pollOpenReadOnly target (rebooted data) = some (.ok (.Ok ⟨4⟩),(recovered data)) := by
    simp [pollOpenReadOnly,target_bytes,
      supportedOpenPath,valid_b,not_directory,rebooted,recovered,reopening,newNames,not_lt.mpr bounded,
      namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,decode,encode,
      limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,handleTypeName]
  simp only [open_readonly,io_core.open_readonly,monadLift_self,openReadOnly]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp

/-- Publication is composed with restart and the actual Rust opener. Every
accepted post-acknowledgment tearing mask preserves the saved contents. -/
theorem publication_restart (mask result : ByteArray)
    (accepted : persist data data mask = some result) :
    publish_file ⟨2⟩ source target (initial data) = (.ok (.Ok ()),(published data)) ∧
    filesystemCrashImage newNames [(1,mask)] (published data) = some ⟨newNames,[(1,data)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,data)],3⟩ reopening = some (rebooted data) ∧
    open_readonly target (rebooted data) = (.ok (.Ok ⟨4⟩),(recovered data)) ∧
    (lookup ⟨4⟩ (recovered data)).map (·.visible) = some data := by
  simp only [limit] at bounded
  refine ⟨publish_contract data bounded,checkpoint_image_all data bounded mask result accepted,
    restart_checkpoint data bounded,recover_published data bounded,?_⟩
  simp [lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,recovered,inode,decode,
    encode,limit,not_lt.mpr bounded,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]


@[expose] def syncError (error : Nat) : Term :=
  .cons (.tuple #[.atom "sync_all",.atom "error",.integer error,.bitstring ByteArray.empty 0])
    (actionOk "close" ByteArray.empty .nil)

@[expose] def failing (error : Nat) (closed : Bool := false) : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,(if closed then closedHandleTypeName else writableHandleTypeName),
      encodeHandle ⟨1,0,(if closed then .nil else syncError error)⟩),
    (1,inodeTypeName,encode ⟨data,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}

@[expose] def failed : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,actionOk "close" ByteArray.empty .nil⟩),
    (1,inodeTypeName,encode ⟨data,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,oldNames,[],renameScript⟩)]}

omit bounded in
theorem persist_empty : persist ByteArray.empty data ByteArray.empty = some ByteArray.empty := by
  simp [persist]
  rfl

theorem failed_sync_poll (error : Nat) : pollSync ⟨2⟩ (failing data error) =
    some (.ok (.Err ⟨error⟩),failed data) := by
  simp only [limit] at bounded
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  simp [pollSync,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,failing,failed,
    syncError,actionOk,inode,decode,encode,limit,not_lt.mpr bounded,blocked,syncStep,
    action,nonnegative,persist_empty,store,sharedStore,encodeNamespace,encodeNames,oldNames,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem failed_close_poll : pollClose ⟨2⟩ (failed data) =
    some (.ok (),failing data 0 true) := by
  simp only [limit] at bounded
  simp [pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,failing,failed,
    syncError,actionOk,inode,decode,encode,limit,not_lt.mpr bounded,blocked,closeStep,
    action,persist_empty,sharedStore,retire,encodeNamespace,encodeNames,oldNames,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,inodeTypeName,namespaceTypeName]

/-- A data synchronization error is returned intact after actual cleanup;
publication does not proceed to rename or acknowledge durability. -/
theorem failed_publication (error : Nat) :
    publish_file ⟨2⟩ source target (failing data error) =
      (.ok (.Err ⟨error⟩),failing data 0 true) := by
  simp only [publish_file,synchronize_then_close,io_core.synchronize,monadLift_self,
    syncAll,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (failed_sync_poll data bounded error)]
  simp only [Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (failed_close_poll data bounded)]
  simp [NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,NativeM.monadLift_eq,
    NativeM.fromRust_ok,core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

omit bounded in
theorem empty_payload : publish_file ⟨2⟩ source target (initial ByteArray.empty) =
    (.ok (.Ok ()),published ByteArray.empty) :=
  publish_contract ByteArray.empty (by simp [limit])

omit bounded in
theorem largest_payload :
    let full : ByteArray := ⟨_root_.Array.replicate limit 0⟩
    publish_file ⟨2⟩ source target (initial full) = (.ok (.Ok ()),published full) := by
  intro full
  exact publish_contract full (by simp [full,ByteArray.size])

omit bounded in
/-- Exceeding the supported payload size exhausts verification before any effect;
it is not modeled as a successful sync or an invented operating-system error. -/
theorem payload_bound (tooLarge : limit < data.size) :
    publish_file ⟨2⟩ source target (initial data) = (.error .exhausted,initial data) := by
  simp only [limit] at tooLarge
  have poll : pollSync ⟨2⟩ (initial data) = some (.error .exhausted,initial data) := by
    simp [pollSync,initial,renameScript,opening,dirScript,actionOk,lookup,sharedLookup,
      getHandle,decodeHandle,encodeHandle,inode,decode,encode,limit,tooLarge,
      pollDirectorySync,directoryHandle,encodeNamespace,encodeNames,oldNames,
      typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName,
      directoryTypeName]
  simp only [publish_file,synchronize_then_close,io_core.synchronize,monadLift_self,
    syncAll,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.error_apply]

end Publish.Payload
