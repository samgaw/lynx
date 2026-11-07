module
public import Publish.WordRecovery
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.Commit
open NativeFile Publish.Properties
open Publish.WordRecovery (wordBytes lowByte highByte word_size)

@[expose] def wire (value : U16) : Slice U8 :=
  Array.to_slice (core.num.U16.to_le_bytes value)
@[expose] def content (value : U16) : ByteArray := bytes (wire value)

theorem content_layout (value : U16) :
    content value = wordBytes (lowByte value) (highByte value) := by
  simp only [content,wire,bytes,Array.val_to_slice,core.num.U16.to_le_bytes,
    Array.from_val,wordBytes,lowByte,highByte,UScalar.val]
  simp only [List.map_toArray,List.map_map]
  change (⟨((value.bv.toLEBytes.map fun x => UInt8.ofNat x.toNat).toArray)⟩ : ByteArray) = _
  rw [BitVec.toLEBytes]
  simp only [Nat.reduceGT,↓reduceIte]
  rw [BitVec.toLEBytes]
  simp only [Nat.reduceSub,Nat.reduceGT,↓reduceIte]
  rw [BitVec.toLEBytes]
  simp only [Nat.reduceGT,↓reduceIte,List.map_cons,List.map_nil]
  have bound : value.bv.toNat < 65536 := value.bv.isLt
  have highBound : value.bv.toNat / 256 < 256 := by omega
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    Nat.reducePow,Nat.mod_eq_of_lt highBound]

theorem content_size (value : U16) : (content value).size = 2 := by
  rw [content_layout,word_size]

theorem wire_length (value : U16) : (wire value).val.length = 2 := by
  simpa [content,bytes,← ByteArray.size_data] using content_size value

theorem stable (value : U16) : persist (content value) (content value) ⟨#[0,0]⟩ = some (content value) := by
  rw [content_layout]
  exact Publish.WordRecovery.stable_bytes _ _

@[expose] def syncScript : Term := actionOk "sync_all" ByteArray.empty
  (actionOk "close" ⟨#[0,0]⟩ .nil)
@[expose] def writeChoice (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom "write",.atom "ok",.integer count,.bitstring ByteArray.empty 0]) rest
@[expose] def createChoice (script : Term) : Term :=
  .cons (.tuple #[.atom "create_new",.bitstring a 0,.atom "ok",.integer 0,script]) renameScript
@[expose] def initial : Environment :=
  {nativeHeap := [(0,namespaceTypeName,encodeNamespace ⟨[],[],[],createChoice (writeChoice 2 syncScript)⟩)]}
@[expose] def created : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,writeChoice 2 syncScript⟩),
    (1,inodeTypeName,encode ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,[],[oldNames],renameScript⟩)]}
@[expose] def written (value : U16) : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,2,syncScript⟩),
    (1,inodeTypeName,encode ⟨content value,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,[],[oldNames],renameScript⟩)]}
@[expose] def synced (value : U16) : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,2,actionOk "close" ⟨#[0,0]⟩ .nil⟩),
    (1,inodeTypeName,encode ⟨content value,content value,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,[],[oldNames],renameScript⟩)]}
@[expose] def closed (value : U16) : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,closedHandleTypeName,encodeHandle ⟨1,2,.nil⟩),
    (1,inodeTypeName,encode ⟨content value,content value,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,[],[oldNames],renameScript⟩)]}
@[expose] def renamed (value : U16) : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,closedHandleTypeName,encodeHandle ⟨1,2,.nil⟩),
    (1,inodeTypeName,encode ⟨content value,content value,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,[],[oldNames,newNames],opening⟩)]}
@[expose] def opened (value : U16) : Environment :=
  {refCounter := 3,nativeHeap := [
    (3,directoryTypeName,.tuple #[dirScript]),
    (2,closedHandleTypeName,encodeHandle ⟨1,2,.nil⟩),
    (1,inodeTypeName,encode ⟨content value,content value,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,[],[oldNames,newNames],.nil⟩)]}
@[expose] def checkpointed (value : U16) : Environment :=
  {refCounter := 3,nativeHeap := [
    (3,directoryTypeName,.tuple #[actionOk "close_dir" ByteArray.empty .nil]),
    (2,closedHandleTypeName,encodeHandle ⟨1,2,.nil⟩),
    (1,inodeTypeName,encode ⟨content value,content value,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩)]}
@[expose] def done (value : U16) : Environment :=
  {refCounter := 3,nativeHeap := [
    (3,closedDirectoryTypeName,.tuple #[.nil]),
    (2,closedHandleTypeName,encodeHandle ⟨1,2,.nil⟩),
    (1,inodeTypeName,encode ⟨content value,content value,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩)]}

theorem create_poll : pollCreateNew source initial = some (.ok (.Ok ⟨2⟩),created) := by
  simp [pollCreateNew,source_bytes,valid_a,initial,createChoice,created,pathChoice,
    namespaceSnapshot,namespaceTable,namespaceHistory,tablesEqual,
    encodeNamespace,encodeNames,oldNames,namespaceTypeName,writableHandleTypeName,inodeTypeName,
    storeNamespace,encodeHandle]

theorem sync_poll (value : U16) : pollSync ⟨2⟩ (written value) = some (.ok (.Ok ()),synced value) := by
  simp [pollSync,written,synced,syncScript,
    lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,limit,
    content_size,blocked,syncStep,action,
    store,sharedStore,
    encodeNamespace,encodeNames,oldNames,
    renameScript,opening,dirScript,actionOk,
    typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem close_poll (value : U16) : pollClose ⟨2⟩ (synced value) = some (.ok (),closed value) := by
  simp [pollClose,synced,closed,
    lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,limit,
    content_size,blocked,closeStep,action,
    stable,sharedStore,retire,
    encodeNamespace,encodeNames,oldNames,
    renameScript,opening,dirScript,actionOk,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem rename_poll (value : U16) : pollRename source target (closed value) = some (.ok (.Ok ()),renamed value) := by
  simp [pollRename,closed,renamed,
    source_bytes,target_bytes,valid_a,valid_b,
    encodeHandle,inode,decode,encode,limit,
    content_size,
    namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    different,renameScript,opening,dirScript,actionOk,
    renameChoice,renamedNames,storeNamespace,
    closedHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem open_poll (value : U16) : pollOpenReadOnly (toStr ".") (renamed value) = some (.ok (.Ok ⟨3⟩),opened value) := by
  simp [pollOpenReadOnly,renamed,opened,
    valid_a,valid_b,
    encodeHandle,encode,
    namespaceSnapshot,namespaceState,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    opening,dirScript,actionOk,
    openChoice,pathChoice,replaceNamespaceScript,
    directory_bytes,supportedOpenPath,
    closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName]

theorem dir_sync_poll (value : U16) : pollSync ⟨3⟩ (opened value) = some (.ok (.Ok ()),checkpointed value) := by
  simp [pollSync,pollDirectorySync,opened,checkpointed,
    valid_a,valid_b,
    lookup,encodeHandle,encode,
    action,
    namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    dirScript,actionOk,
    storeNamespace,
    directoryHandle,storeDirectory,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName]

theorem dir_close_poll (value : U16) : pollClose ⟨3⟩ (checkpointed value) = some (.ok (),done value) := by
  simp [pollClose,pollDirectoryClose,checkpointed,done,
    lookup,encodeHandle,encode,
    action,
    encodeNamespace,encodeNames,newNames,
    actionOk,
    directoryHandle,storeDirectory,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

theorem write_poll (value : U16) : pollWrite ⟨2⟩ (wire value) created =
    some (.ok (.Ok 2#usize,⟨2⟩),written value) := by
  have found : lookup ⟨2⟩ created = some ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2 syncScript⟩ := by
    simp [lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,created,inode,decode,encode,
      limit,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]
  have writable : getHandle ⟨2⟩ handleTypeName created = none := by
    simp [getHandle,created,handleTypeName,writableHandleTypeName]
  have step : writeStep ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2 syncScript⟩ (wire value) =
      some (.Ok 2#usize,⟨content value,ByteArray.empty,2,syncScript⟩) := by
    simp [writeStep,wire_length,writeChoice,action,limit,overwrite,Payload.persist_empty]
    constructor
    · rfl
    · have length : (bytes (wire value)).data.toList.length = 2 := by
        simpa [content,← ByteArray.size_data] using content_size value
      rw [← length,List.take_length]
      rfl
  have ready : blocked ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2 syncScript⟩ = false := rfl
  simp only [pollWrite,found,ready,Bool.false_eq_true,↓reduceIte,step,writable]
  simp [store,sharedStore,created,written,encodeHandle,decodeHandle,encode,namespaceTypeName,
    writableHandleTypeName,inodeTypeName,typeName]

/-- The actual Rust publication helper consumes the written file and checkpoints its name. -/
theorem publish_written (value : U16) :
    publish_file ⟨2⟩ source target (written value) = (.ok (.Ok ()),done value) := by
  simp only [publish_file,synchronize_then_close,sync_directory,io_core.synchronize,
    io_core.rename_file,io_core.open_readonly,monadLift_self,NativeOwnedDrop.drop,
    syncAll,close,NativeFile.rename,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (sync_poll value)]
  simp only [Result.ok_bind,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll value)]
  simp only [Result.ok_bind,NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (rename_poll value)]
  simp only [Result.ok_bind,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll value)]
  simp only [Result.ok_bind,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (dir_sync_poll value)]
  simp only [Result.ok_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (dir_close_poll value)]
  simp []

/-- Every u16 value is encoded, fully written and durably published by the extracted Rust. -/
theorem commit_contract (value : U16) :
    commit_word source target value initial = (.ok (.Ok true),done value) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ create_poll]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp only [NativeM.lift,Result.ok_bind]
  simp only [io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := write_poll value
  unfold wire at wrote
  rw [Result.wait_ready_apply _ _ _ _ _ wrote]
  simp only [Result.ok_bind]
  simp only [show (2#usize).val = 2 from rfl]
  simp only [publish_file,synchronize_then_close,sync_directory,io_core.synchronize,
    io_core.rename_file,io_core.open_readonly,monadLift_self,NativeOwnedDrop.drop,
    syncAll,close,NativeFile.rename,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (sync_poll value)]
  simp only [Result.ok_bind,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll value)]
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (rename_poll value)]
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll value)]
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.fromRust_ok]
  rw [Result.wait_ready_apply _ _ _ _ _ (dir_sync_poll value)]
  simp only [Result.ok_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (dir_close_poll value)]
  simp []

/-- The unsynchronized written state is a prefix of the actual Rust execution. -/
theorem write_prefix (value : U16) : ∃ residual,
    Result.ReadyPrefix (commit_word source target value) initial residual (written value) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ create_poll
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,NativeM.lift]
  simp only [Result.ok_bind,io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := write_poll value
  unfold wire at wrote
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ wrote
  exact ⟨_,.refl _ _⟩

/-- Before synchronization, both the temporary name and all written bytes may be lost. -/
theorem unsynced_loss (value : U16) :
    filesystemCrashImage [] [(1,ByteArray.empty)] (written value) =
      some ⟨[],[(1,ByteArray.empty)],2⟩ := by
  simp [filesystemCrashImage,written,namespaceSnapshot,namespaceTable,namespaceHistory,
    namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,oldNames,valid_a,content_size,inode,decode,encode,
    encodeHandle,limit,Payload.persist_empty,inodeTypeName,namespaceTypeName,writableHandleTypeName]

/-- Acknowledgement leaves both bytes and the published name durable. -/
theorem committed_image (value : U16) (mask result : ByteArray)
    (accepted : persist (content value) (content value) mask = some result) :
    filesystemCrashImage newNames [(1,mask)] (done value) =
      some ⟨newNames,[(1,content value)],3⟩ := by
  have same := persist_same (content value) mask result accepted
  subst result
  simp [filesystemCrashImage,done,namespaceSnapshot,namespaceTable,namespaceHistory,
    namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,newNames,valid_b,content_size,inode,decode,encode,
    encodeHandle,limit,accepted,inodeTypeName,namespaceTypeName,closedDirectoryTypeName,
    closedHandleTypeName]

/-- Actual creation, encoding, write, publication and parsed recovery compose for every u16. -/
theorem commit_recovery (value : U16) (mask result : ByteArray)
    (accepted : persist (content value) (content value) mask = some result) :
    commit_word source target value initial = (.ok (.Ok true),done value) ∧
    filesystemCrashImage newNames [(1,mask)] (done value) =
      some ⟨newNames,[(1,content value)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,content value)],3⟩ Publish.NamedRecovery.openingScript =
      some (Publish.WordRecovery.boot (lowByte value) (highByte value)) ∧
    recover_named_word target (Publish.WordRecovery.boot (lowByte value) (highByte value)) =
      (.ok (.Ok (some value)),Publish.WordRecovery.scan (lowByte value) (highByte value) 2 .nil true) := by
  refine ⟨commit_contract value,committed_image value mask result accepted,?_,Publish.WordRecovery.recover_value value⟩
  rw [content_layout]
  exact (Publish.WordRecovery.publication_recovery (lowByte value) (highByte value) mask result
    (by simpa only [content_layout] using accepted)).2.2.1

end Publish.Commit
