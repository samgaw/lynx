module
public import Publish.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.NamedRecovery
open NativeFile Publish.Properties

@[expose] def closeScript : Term := actionOk "close" ⟨#[0,0]⟩ .nil
@[expose] def readChoice (rest : Term) : Term :=
  .cons (.tuple #[.atom "read",.atom "ok",.integer 1,.bitstring ⟨#[0,0]⟩ 0]) rest
@[expose] def readScript : Term := readChoice (readChoice closeScript)
@[expose] def openingScript : Term :=
  .cons (.tuple #[.atom "open",.bitstring b 0,.atom "ok",.integer 0,readScript]) .nil
@[expose] def boot : Environment :=
  {refCounter := 3,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],openingScript⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩)]}
@[expose] def scan (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {refCounter := 4,nativeHeap := [
    (4,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩),
    (1,inodeTypeName,encode ⟨content,content,0,.nil⟩)]}
@[expose] def one (byte : U8) : Slice U8 := Slice.from [byte] (by scalar_tac)

theorem decoded_word : core.num.U16.from_le_bytes (Array.make 2#usize [7#u8,0#u8]) = 7#u16 := by
  decide +kernel

theorem open_poll : pollOpenReadOnly target boot = some (.ok (.Ok ⟨4⟩),scan 0 readScript) := by
  simp [pollOpenReadOnly,target_bytes,supportedOpenPath,valid_b,boot,scan,openingScript,
    readScript,readChoice,closeScript,actionOk,newNames,content_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,
    handleTypeName]
  decide +kernel

theorem first_poll : pollRead ⟨4⟩ (one 0#u8) (scan 0 readScript) =
    some (.ok (.Ok 1#usize,⟨4⟩,one 7#u8),scan 1 (readChoice closeScript)) := by
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,content_size,blocked,readStep,readBuffer,readScript,readChoice,
    closeScript,actionOk,action,stable_content,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [content,Data.ListN.ListN.from_to_inverse]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem second_poll : pollRead ⟨4⟩ (one 0#u8) (scan 1 (readChoice closeScript)) =
    some (.ok (.Ok 1#usize,⟨4⟩,one 0#u8),scan 2 closeScript) := by
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,content_size,blocked,readStep,readBuffer,readChoice,
    closeScript,actionOk,action,stable_content,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [content,Data.ListN.ListN.from_to_inverse]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem close_poll : pollClose ⟨4⟩ (scan 2 closeScript) = some (.ok (),scan 2 .nil true) := by
  simp [pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,content_size,blocked,closeStep,closeScript,actionOk,action,
    stable_content,sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem read_next {α : Type} (env updated : Environment) (buffer output : Slice U8)
    (reply : core.result.Result Usize NativeIoError)
    (ready : pollRead ⟨4⟩ buffer env = some (.ok (reply,⟨4⟩,output),updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (io_core.read_once ⟨4⟩ buffer >>= next) env = next (reply,⟨4⟩,output) updated := by
  simp only [io_core.read_once,monadLift_self,NativeFile.read,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- The actual parser reads both bytes from the shared named inode. -/
theorem parsed_word : read_word ⟨4⟩ (scan 0 readScript) =
    (.ok (.Ok (some 7#u16),⟨4⟩),scan 2 closeScript) := by
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _) _ = _
  rw [read_next _ _ _ _ _ first_poll]
  change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _) _ = _
  rw [read_next _ _ _ _ _ second_poll]
  simp [decoded_word,NativeM.ok,NativeM.lift,Array.from_slice,Array.to_slice_mut,
    one,Array.make_val,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
    Result.ok_bind,Result.ok_apply]

/-- Composes Rust parsing with actual destruction of its owned handle. -/
theorem parse_and_close : read_and_close_word ⟨4⟩ (scan 0 readScript) =
    (.ok (.Ok (some 7#u16)),scan 2 .nil true) := by
  have parser {α : Type} (next : _ → NativeM α) :
      (read_word ⟨4⟩ >>= next) (scan 0 readScript) =
        next (.Ok (some 7#u16),⟨4⟩) (scan 2 closeScript) := by
    simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
      Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
    change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _) _ = _
    rw [read_next _ _ _ _ _ first_poll]
    simp [bind_assoc]
    change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _) _ = _
    rw [read_next _ _ _ _ _ second_poll]
    simp [decoded_word,NativeM.ok,NativeM.lift,Array.from_slice,Array.to_slice_mut,
      one,Array.make_val,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
      Result.ok_bind,Result.ok_apply]
  simp only [read_and_close_word,monadLift_self]
  rw [parser]
  simp only [NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ close_poll]
  simp [NativeM.ok]

/-- Opening, decoding and scope cleanup use extracted first-party Rust code. -/
theorem recover_word : recover_named_word target boot =
    (.ok (.Ok (some 7#u16)),scan 2 .nil true) := by
  simp only [recover_named_word,io_core.open_readonly,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ open_poll]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  exact parse_and_close

/-- Every accepted post-publication byte mask composes with actual parsed recovery. -/
theorem publication_recovery (mask result : ByteArray)
    (accepted : persist content content mask = some result) :
    publish_file ⟨2⟩ source target initial = (.ok (.Ok ()),published) ∧
    filesystemCrashImage newNames [(1,mask)] published = some ⟨newNames,[(1,content)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,content)],3⟩ openingScript = some boot ∧
    recover_named_word target boot = (.ok (.Ok (some 7#u16)),scan 2 .nil true) := by
  exact ⟨publish_contract,checkpoint_image_all mask result accepted,rfl,recover_word⟩

@[expose] def readError (error : Nat) : Term :=
  .cons (.tuple #[.atom "read",.atom "error",.integer error,.bitstring ⟨#[0,0]⟩ 0]) closeScript

theorem error_poll (error : Nat) : pollRead ⟨4⟩ (one 0#u8) (scan 0 (readError error)) =
    some (.ok (.Err ⟨error⟩,⟨4⟩,one 0#u8),scan 0 closeScript) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,content_size,blocked,readStep,readError,closeScript,actionOk,
    action,nonnegative,stable_content,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem close_error_path : pollClose ⟨4⟩ (scan 0 closeScript) = some (.ok (),scan 0 .nil true) := by
  simp [pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,content_size,blocked,closeStep,closeScript,actionOk,action,
    stable_content,sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

/-- Read errors are returned intact and the actual Rust cleanup still consumes
its owned capability, rather than reporting a successful decoded word. -/
theorem read_error_cleanup (error : Nat) :
    read_and_close_word ⟨4⟩ (scan 0 (readError error)) =
      (.ok (.Err ⟨error⟩),scan 0 .nil true) := by
  simp only [read_and_close_word,read_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _) _ = _
  rw [read_next _ _ _ _ _ (error_poll error)]
  simp only [NativeM.ok,Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ close_error_path]
  simp [NativeM.ok]

end Publish.NamedRecovery
