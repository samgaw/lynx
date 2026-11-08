module
public import Rename.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Rename.Properties
open NativeFile

@[expose] def source : Str := Slice.from [97#u8] (by scalar_tac)
@[expose] def target : Str := Slice.from [98#u8] (by scalar_tac)
@[expose] def sourceBytes : ByteArray := ⟨#[97]⟩
@[expose] def targetBytes : ByteArray := ⟨#[98]⟩
@[expose] def originalNames : Names := [(sourceBytes,1),(targetBytes,2)]
@[expose] def replacedNames : Names := [(targetBytes,1)]
@[expose] def choice (success : Bool) (error : Nat) (applied : Bool) (rest : Term) : Term :=
  .cons (.tuple #[.atom "rename",.bitstring sourceBytes 0,.bitstring targetBytes 0,
    .atom (if success then "ok" else "error"),.integer error,
    .atom (if applied then "apply" else "keep")]) rest
@[expose] def node (id : Nat) (state : State) : Nat × String × Term :=
  (id,inodeTypeName,encode {state with position := 0, script := .nil})
@[expose] def world (first second : State) (names : Names) (pending : List Names) (script : Term) : Environment :=
  {nativeRefCounter := 4,nativeHeap := [
    (3,handleTypeName,encodeHandle ⟨1,0,.nil⟩),
    (4,handleTypeName,encodeHandle ⟨2,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨names,originalNames,pending,script⟩),
    node 1 first,node 2 second]}

@[expose] def Bounded (state : State) : Prop := state.visible.size ≤ limit ∧ state.durable.size ≤ limit

theorem source_bytes : bytes source = sourceBytes := by
  simp [bytes,source,Slice.from,Slice.val,sourceBytes,Data.ListN.ListN.from_to_inverse]

theorem target_bytes : bytes target = targetBytes := by
  simp [bytes,target,Slice.from,Slice.val,targetBytes,Data.ListN.ListN.from_to_inverse]

theorem source_valid : supportedPath sourceBytes = true := by decide
theorem target_valid : supportedPath targetBytes = true := by decide
theorem different : (sourceBytes.data == targetBytes.data) = false := by decide
theorem different_rev : (targetBytes.data == sourceBytes.data) = false := by decide

/-- The actual cross-crate rename changes names, not inode contents or open
capabilities, and does not advance the directory synchronization checkpoint. -/
theorem replace_next {α : Type} (first second : State) (validFirst : Bounded first) (validSecond : Bounded second)
    (success : Bool) (error : Nat) (status : success = true → error = 0) (rest : Term)
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (rename_visible source target >>= next)
      (world first second originalNames [] (choice success error true rest)) =
      next (if success then .Ok () else .Err ⟨error⟩)
        (world first second replacedNames [replacedNames] rest) := by
  obtain ⟨firstVisible,firstDurable⟩ := validFirst
  obtain ⟨secondVisible,secondDurable⟩ := validSecond
  simp only [limit] at firstVisible firstDurable secondVisible secondDurable
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  have poll : pollRename source target
      (world first second originalNames [] (choice success error true rest)) =
      some (.ok (if success then .Ok () else .Err ⟨error⟩),
        world first second replacedNames [replacedNames] rest) := by
    cases success
    all_goals simp [status,nonnegative,pollRename,source_bytes,target_bytes,source_valid,target_valid,
      world,choice,renameChoice,namespaceSnapshot,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,tablesEqual,originalNames,replacedNames,
      List.eraseDups_cons,different,different_rev,inode,node,decode,encode,limit,
      not_lt.mpr firstVisible,not_lt.mpr firstDurable,not_lt.mpr secondVisible,
      not_lt.mpr secondDurable,storeNamespace,renamedNames,
      namespaceTypeName,handleTypeName,inodeTypeName]
  simp only [rename_visible,io_core.rename_file,monadLift_self,NativeFile.rename,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

/-- An admitted I/O error can still publish the replacement. -/
theorem error_can_apply (first second : State) (validFirst : Bounded first) (validSecond : Bounded second)
    (error : Nat) (rest : Term) :
    rename_visible source target (world first second originalNames [] (choice false error true rest)) =
      (.ok (.Err ⟨error⟩),world first second replacedNames [replacedNames] rest) := by
  have returned := replace_next first second validFirst validSecond false error (by simp) rest Result.ok
  simpa [Result.bind_ok,Result.ok_apply] using returned

theorem successful_replace (first second : State) (validFirst : Bounded first) (validSecond : Bounded second)
    (rest : Term) :
    rename_visible source target (world first second originalNames [] (choice true 0 true rest)) =
      (.ok (.Ok ()),world first second replacedNames [replacedNames] rest) := by
  have returned := replace_next first second validFirst validSecond true 0 (by simp) rest Result.ok
  simpa [Result.bind_ok,Result.ok_apply] using returned

theorem unlinked_handle (first second : State) (validFirst : Bounded first) (validSecond : Bounded second)
    (rest : Term) :
    lookup ⟨3⟩ (world first second replacedNames [replacedNames] rest) =
      some {first with position := 0, script := .nil} ∧
    lookup ⟨4⟩ (world first second replacedNames [replacedNames] rest) =
      some {second with position := 0, script := .nil} := by
  obtain ⟨a,b⟩ := validFirst
  obtain ⟨c,d⟩ := validSecond
  simp only [limit] at a b c d
  simp [lookup,world,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,node,decode,encode,
    not_lt.mpr a,not_lt.mpr b,not_lt.mpr c,not_lt.mpr d,limit,
    typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem replaced_capabilities (first second : State) (validFirst : Bounded first) (validSecond : Bounded second)
    (rest : Term) :
    rename_visible source target (world first second originalNames [] (choice true 0 true rest)) =
      (.ok (.Ok ()),world first second replacedNames [replacedNames] rest) ∧
    lookup ⟨3⟩ (world first second replacedNames [replacedNames] rest) =
      some {first with position := 0, script := .nil} ∧
    lookup ⟨4⟩ (world first second replacedNames [replacedNames] rest) =
      some {second with position := 0, script := .nil} :=
  ⟨successful_replace first second validFirst validSecond rest,
    unlinked_handle first second validFirst validSecond rest⟩

/-- A no-effect error leaves inode contents and names intact. Other admitted
errors can apply the mutation, as shown by error_can_apply. -/
theorem error_keeps_names (first second : State) (error : Nat) (rest : Term) :
    rename_visible source target (world first second originalNames [] (choice false error false rest)) =
      (.ok (.Err ⟨error⟩),world first second originalNames [] rest) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  have poll : pollRename source target
      (world first second originalNames [] (choice false error false rest)) =
      some (.ok (.Err ⟨error⟩),world first second originalNames [] rest) := by
    simp [pollRename,source_bytes,target_bytes,source_valid,target_valid,world,choice,
      renameChoice,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,tablesEqual,originalNames,List.eraseDups_cons,
      different,different_rev,nonnegative,replaceNamespaceScript,node,
      namespaceTypeName,handleTypeName,inodeTypeName]
  simp only [rename_visible,io_core.rename_file,monadLift_self,NativeFile.rename]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_apply]

@[expose] def aliasNames : Names := [(sourceBytes,1),(targetBytes,1)]
@[expose] def aliases (state : State) (script : Term) : Environment :=
  {nativeRefCounter := 1,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨aliasNames,aliasNames,[],script⟩),node 1 state]}

theorem same_inode_noop (state : State) (valid : Bounded state) (rest : Term) :
    rename_visible source target (aliases state (choice true 0 true rest)) =
      (.ok (.Ok ()),aliases state rest) := by
  obtain ⟨visible,durable⟩ := valid
  simp only [limit] at visible durable
  have poll : pollRename source target (aliases state (choice true 0 true rest)) =
      some (.ok (.Ok ()),aliases state rest) := by
    simp [pollRename,source_bytes,target_bytes,source_valid,target_valid,aliases,aliasNames,
      choice,renameChoice,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,different,different_rev,
      inode,node,decode,encode,limit,not_lt.mpr visible,not_lt.mpr durable,
      namespaceTypeName,inodeTypeName,replaceNamespaceScript]
  simp only [rename_visible,io_core.rename_file,monadLift_self,NativeFile.rename]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_apply]

end Rename.Properties
