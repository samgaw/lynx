module
public import Create.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Create.Properties
open NativeFile

@[expose] def path : Str := Slice.from [100#u8,97#u8,116#u8,97#u8] (by scalar_tac)
@[expose] def nameBytes : ByteArray := ⟨#[100,97,116,97]⟩
@[expose] def choice (success : Bool) (error : Nat) (script rest : Term) : Term :=
  .cons (.tuple #[.atom "create_new", .bitstring nameBytes 0,
    .atom (if success then "ok" else "error"), .integer error, script]) rest
@[expose] def names : Names := [(nameBytes,1)]
@[expose] def initial (script : Term) : Environment :=
  {nativeHeap := [(0,namespaceTypeName,encodeNamespace ⟨[],[],[],script⟩)]}
@[expose] def created (script rest : Term) : Environment :=
  {refCounter := 2, nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,script⟩),
    (1,inodeTypeName,encode ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨names,[],[names],rest⟩)]}

theorem path_bytes : bytes path = nameBytes := by
  simp [bytes,path,Slice.from,Slice.val,nameBytes]
  decide

theorem valid_name : supportedPath nameBytes = true := by decide

/-- The actual two-crate exclusive factory allocates a fresh inode and capability
without making the directory entry durable. -/
theorem create_next {α : Type} (script rest : Term)
    (next : core.result.Result NativeFile NativeIoError → NativeM α) :
    (create_fresh path >>= next) (initial (choice true 0 script rest)) =
      next (.Ok ⟨2⟩) (created script rest) := by
  have poll : pollCreateNew path (initial (choice true 0 script rest)) =
      some (.ok (.Ok ⟨2⟩), created script rest) := by
    simp [pollCreateNew,path_bytes,valid_name,initial,choice,pathChoice,
      namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,
      encodeNamespace,encodeNames,storeNamespace,created,names,
      namespaceTypeName,writableHandleTypeName,inodeTypeName,encodeHandle]
  simp only [create_fresh,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

theorem pending_name (script rest : Term) :
    namespaceSnapshot (created script rest) = some ⟨names,[],[names],rest⟩ := by
  simp [namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,
    created,names,encodeNamespace,encodeNames,List.eraseDups_cons,
    namespaceTypeName,writableHandleTypeName,inodeTypeName,encodeHandle,valid_name]

/-- The successful Rust return does not advance the directory synchronization checkpoint. -/
theorem not_directory_synced (script rest : Term) :
    create_fresh path (initial (choice true 0 script rest)) =
      (.ok (.Ok ⟨2⟩), created script rest) ∧
      (namespaceSnapshot (created script rest)).map (·.committed) = some [] := by
  constructor
  · have returned := create_next script rest Result.ok
    simpa [Result.bind_ok,Result.ok_apply] using returned
  · rw [pending_name]
    rfl

@[expose] def occupied (script : Term) : Environment :=
  {refCounter := 1, nativeHeap := [
    (1,inodeTypeName,encode ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨names,names,[],script⟩)]}

theorem existing_success_exhausts (script rest : Term) :
    create_fresh path (occupied (choice true 0 script rest)) =
      (.error .exhausted, occupied (choice true 0 script rest)) := by
  have poll : pollCreateNew path (occupied (choice true 0 script rest)) =
      some (.error .exhausted, occupied (choice true 0 script rest)) := by
    simp [pollCreateNew,path_bytes,valid_name,occupied,choice,pathChoice,
      namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,
      encodeNamespace,encodeNames,names,List.eraseDups_cons,
      namespaceTypeName,inodeTypeName]
  simp only [create_fresh,io_core.create_new_file,monadLift_self,createNew]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.error_apply]

/-- An admitted exclusive-creation error preserves the pre-existing inode and
both namespace tables; it consumes only the host outcome. -/
theorem existing_error (error : Nat) (rest : Term) :
    create_fresh path (occupied (choice false error .nil rest)) =
      (.ok (.Err ⟨error⟩), occupied rest) := by
  have poll : pollCreateNew path (occupied (choice false error .nil rest)) =
      some (.ok (.Err ⟨error⟩), occupied rest) := by
    have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
    simp [pollCreateNew,path_bytes,valid_name,occupied,choice,pathChoice,nonnegative,
      namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,
      encodeNamespace,encodeNames,replaceNamespaceScript,names,List.eraseDups_cons,
      namespaceTypeName,inodeTypeName]
  simp only [create_fresh,io_core.create_new_file,monadLift_self,createNew]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_apply]

/-- The newly allocated read/write capability is usable by the actual low-level
Rust writer. Namespace durability is independent of these file data effects. -/
theorem write_created_next {α : Type} (data : Slice U8) (script rest : Term)
    (count : Usize) (after : State)
    (ready : blocked ⟨ByteArray.empty,ByteArray.empty,0,script⟩ = false)
    (step : writeStep ⟨ByteArray.empty,ByteArray.empty,0,script⟩ data = some (.Ok count,after))
    (next : core.result.Result Usize NativeIoError × NativeFile → NativeM α) :
    (io_core.write_once ⟨2⟩ data >>= next) (created script rest) =
      next (.Ok count,⟨2⟩) (store ⟨2⟩ after (created script rest)) := by
  have found : lookup ⟨2⟩ (created script rest) =
      some ⟨ByteArray.empty,ByteArray.empty,0,script⟩ := by
    simp [lookup,sharedLookup,getHandle,decodeHandle,created,inode,decode,encode,limit,
      namespaceTypeName,writableHandleTypeName,handleTypeName,inodeTypeName,typeName,encodeHandle]
  have writable : getHandle ⟨2⟩ handleTypeName (created script rest) = none := by
    simp [getHandle,created,writableHandleTypeName,handleTypeName]
  have poll : pollWrite ⟨2⟩ data (created script rest) =
      some (.ok (.Ok count,⟨2⟩), store ⟨2⟩ after (created script rest)) := by
    simp [-getHandle,pollWrite,found,ready,step,writable]
  simp only [io_core.write_once,monadLift_self,NativeFile.write,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

/-- The namespace capacity is a verification cutoff, not an invented OS error. -/
theorem namespace_bound (entries : Array Term) (script : Term) (large : 1024 < entries.size) :
    let env : Environment := {nativeHeap := [(0,namespaceTypeName,
      .tuple #[.tuple entries,.tuple #[],.nil,script])]}
    create_fresh path env = (.error .exhausted,env) := by
  intro env
  have poll : pollCreateNew path env = some (.error .exhausted,env) := by
    simp [env,pollCreateNew,path_bytes,valid_name,namespaceSnapshot,namespaceTable,
      namespaceTypeName,large]
  simp only [create_fresh,io_core.create_new_file,monadLift_self,createNew]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.error_apply]

end Create.Properties
