module
public import Publish.Commit
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.Commit.Rejected
open NativeFile Publish.Properties

@[expose] def closeScript : Term := actionOk "close" ByteArray.empty .nil
@[expose] def attempt (success : Bool) (count : Nat) : Term :=
  .cons (.tuple #[.atom "write",.atom (if success then "ok" else "error"),
    .integer count,.bitstring ByteArray.empty 0]) closeScript
@[expose] def start (script : Term) : Environment :=
  {nativeHeap := [(0,namespaceTypeName,encodeNamespace ⟨[],[],[],createChoice script⟩)]}
@[expose] def world (data : ByteArray) (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {refCounter := 2,nativeHeap := [
    (2,(if closed then closedHandleTypeName else writableHandleTypeName),encodeHandle ⟨1,position,script⟩),
    (1,inodeTypeName,encode ⟨data,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨oldNames,[],[oldNames],renameScript⟩)]}
@[expose] def prefixBytes (value : U16) (count : Nat) : ByteArray :=
  ⟨((content value).data.toList.take count).toArray⟩

theorem prefixBytes_bound (value : U16) (count : Nat) (short : count ≤ 1) :
    (prefixBytes value count).size ≤ limit := by
  change ((content value).data.toList.take count).toArray.size ≤ limit
  simp only [List.size_toArray,List.length_take,limit]
  omega

theorem created_poll (script : Term) :
    pollCreateNew source (start script) = some (.ok (.Ok ⟨2⟩),world ByteArray.empty 0 script) := by
  simp [pollCreateNew,source_bytes,valid_a,start,createChoice,world,pathChoice,
    namespaceSnapshot,namespaceTable,namespaceHistory,tablesEqual,
    encodeNamespace,encodeNames,oldNames,namespaceTypeName,writableHandleTypeName,inodeTypeName,
    storeNamespace,encodeHandle]

theorem error_poll (value : U16) (code : Nat) :
    pollWrite ⟨2⟩ (wire value) (world ByteArray.empty 0 (attempt false code)) =
      some (.ok (.Err ⟨code⟩,⟨2⟩),world ByteArray.empty 0 closeScript) := by
  simp [pollWrite,world,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,
    limit,not_lt.mpr (Int.natCast_nonneg code),blocked,attempt,action,writeStep,wire_length,Payload.persist_empty,store,sharedStore,
    writableHandleTypeName,handleTypeName,typeName,inodeTypeName,namespaceTypeName]

theorem zero_poll (value : U16) :
    pollWrite ⟨2⟩ (wire value) (world ByteArray.empty 0 (attempt true 0)) =
      some (.ok (.Ok 0#usize,⟨2⟩),world ByteArray.empty 0 closeScript) := by
  simp [pollWrite,world,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,
    limit,Int.natCast_nonneg,blocked,attempt,action,writeStep,wire_length,overwrite,Payload.persist_empty,store,sharedStore,
    writableHandleTypeName,handleTypeName,typeName,inodeTypeName,namespaceTypeName]
  rfl

theorem one_poll (value : U16) :
    pollWrite ⟨2⟩ (wire value) (world ByteArray.empty 0 (attempt true 1)) =
      some (.ok (.Ok 1#usize,⟨2⟩),world (prefixBytes value 1) 1 closeScript) := by
  simp [pollWrite,world,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,
    limit,Int.natCast_nonneg,blocked,attempt,action,writeStep,wire_length,overwrite,Payload.persist_empty,store,sharedStore,
    prefixBytes,content,writableHandleTypeName,handleTypeName,typeName,inodeTypeName,namespaceTypeName]
  rfl

theorem close_poll (data : ByteArray) (position : Nat) (bounded : data.size ≤ limit) (positionBound : position ≤ limit) :
    pollClose ⟨2⟩ (world data position closeScript) =
      some (.ok (),world data position .nil true) := by
  simp only [limit] at bounded positionBound
  simp [pollClose,world,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,
    limit,not_lt.mpr (Int.natCast_nonneg position),not_lt.mpr bounded,not_lt.mpr positionBound,blocked,closeScript,actionOk,action,closeStep,Payload.persist_empty,
    sharedStore,retire,writableHandleTypeName,handleTypeName,closedHandleTypeName,typeName,inodeTypeName,
    namespaceTypeName]

/-- An actual Rust write error is propagated after closing, with no publication or synchronization. -/
theorem write_error (value : U16) (code : Nat) :
    commit_word source target value (start (attempt false code)) =
      (.ok (.Err ⟨code⟩),world ByteArray.empty 0 .nil true) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (created_poll _)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,NativeM.lift]
  simp only [Result.ok_bind,io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := error_poll value code
  unfold wire at wrote
  rw [Result.wait_ready_apply _ _ _ _ _ wrote]
  simp only [Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll ByteArray.empty 0 (by simp [limit]) (by simp [limit]))]
  simp [NativeM.ok]

/-- A zero-byte successful write does not acknowledge or publish. -/
theorem zero_write (value : U16) :
    commit_word source target value (start (attempt true 0)) =
      (.ok (.Ok false),world ByteArray.empty 0 .nil true) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (created_poll _)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,NativeM.lift]
  simp only [Result.ok_bind,io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := zero_poll value
  unfold wire at wrote
  rw [Result.wait_ready_apply _ _ _ _ _ wrote]
  simp only [Result.ok_bind,show (0#usize).val = 0 from rfl,
    NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll ByteArray.empty 0 (by simp [limit]) (by simp [limit]))]
  simp [NativeM.ok]

/-- A one-byte successful write closes and leaves only an uncommitted temporary name. -/
theorem short_write (value : U16) :
    commit_word source target value (start (attempt true 1)) =
      (.ok (.Ok false),world (prefixBytes value 1) 1 .nil true) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (created_poll _)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,NativeM.lift]
  simp only [Result.ok_bind,io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := one_poll value
  unfold wire at wrote
  rw [Result.wait_ready_apply _ _ _ _ _ wrote]
  simp only [Result.ok_bind,show (1#usize).val = 1 from rfl,
    NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll _ 1 (prefixBytes_bound value 1 (by omega)) (by simp [limit]))]
  simp [NativeM.ok]

end Publish.Commit.Rejected
