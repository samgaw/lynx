module
public import Directory.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Directory.Properties
open NativeFile

@[expose] def fileName : ByteArray := ⟨#[100,97,116,97]⟩
@[expose] def directoryName : ByteArray := ⟨#[46]⟩
@[expose] def names : Names := [(fileName,1)]
@[expose] def ns (committed : Bool) (script : Term) : Term :=
  encodeNamespace ⟨names,(if committed then names else []),(if committed then [] else [names]),script⟩
@[expose] def node (state : State) : Nat × String × Term :=
  (1,inodeTypeName,encode {state with position := 0, script := .nil})
@[expose] def initial (state : State) (script : Term) : Environment :=
  {nativeRefCounter := 1,nativeHeap := [(0,namespaceTypeName,ns false script),node state]}
@[expose] def world (state : State) (committed closed : Bool) (script rest : Term) : Environment :=
  {nativeRefCounter := 2,nativeHeap := [
    (2,(if closed then closedDirectoryTypeName else directoryTypeName),.tuple #[script]),
    (0,namespaceTypeName,ns committed rest),node state]}
@[expose] def opening (script rest : Term) : Term :=
  .cons (.tuple #[.atom "open",.bitstring directoryName 0,.atom "ok",.integer 0,script]) rest
@[expose] def outcome (op : String) (success : Bool) (error : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom op,.atom (if success then "ok" else "error"),.integer error,
    .bitstring ByteArray.empty 0]) rest

theorem directory_bytes : bytes (toStr ".") = directoryName := by
  simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,directoryName]
  exact ⟨46, by decide +kernel, by decide +kernel⟩

theorem file_name : supportedPath fileName = true := by decide

theorem open_next {α : Type} (state : State) (script rest : Term)
    (next : core.result.Result NativeFile NativeIoError → NativeM α) :
    (io_core.open_readonly (toStr ".") >>= next) (initial state (opening script rest)) =
      next (.Ok ⟨2⟩) (world state false false script rest) := by
  have poll : pollOpenReadOnly (toStr ".") (initial state (opening script rest)) =
      some (.ok (.Ok ⟨2⟩),world state false false script rest) := by
    simp [pollOpenReadOnly,supportedOpenPath,directory_bytes,directoryName,initial,opening,
      world,ns,names,namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,file_name,
      openChoice,pathChoice,replaceNamespaceScript,node,namespaceTypeName,directoryTypeName]
  simp only [io_core.open_readonly,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

theorem sync_next {α : Type} (state : State) (success : Bool) (error : Nat)
    (status : success = true → error = 0) (script rest : Term)
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (io_core.synchronize ⟨2⟩ >>= next)
      (world state false false (outcome "sync_dir" success error script) rest) =
      next (if success then .Ok () else .Err ⟨error⟩) (world state success false script rest) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  have poll : pollSync ⟨2⟩ (world state false false (outcome "sync_dir" success error script) rest) =
      some (.ok (if success then .Ok () else .Err ⟨error⟩),world state success false script rest) := by
    cases success <;> simp [status,nonnegative,pollSync,lookup,pollDirectorySync,directoryHandle,
      world,ns,names,node,outcome,action,namespaceSnapshot,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,file_name,
      storeDirectory,storeNamespace,typeName,handleTypeName,writableHandleTypeName,
      namespaceTypeName,directoryTypeName]
  simp only [io_core.synchronize,monadLift_self,syncAll,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

theorem drop_next {α : Type} (state : State) (committed success : Bool) (error : Nat)
    (status : success = true → error = 0) (script rest : Term) (next : Unit → NativeM α) :
    (NativeOwnedDrop.drop (⟨2⟩ : NativeFile) >>= next)
      (world state committed false (outcome "close_dir" success error script) rest) =
      next () (world state committed true script rest) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  have poll : pollClose ⟨2⟩ (world state committed false (outcome "close_dir" success error script) rest) =
      some (.ok (),world state committed true script rest) := by
    cases success <;> simp [status,nonnegative,pollClose,lookup,pollDirectoryClose,directoryHandle,
      world,node,outcome,action,storeDirectory,typeName,handleTypeName,writableHandleTypeName,
      directoryTypeName,closedDirectoryTypeName]
  simp only [NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

/-- Actual opening, directory sync and compiler-generated scope-exit cleanup
compose across crates. File bytes are preserved on either sync result. -/
theorem sync_directory_contract (state : State) (success : Bool) (error : Nat)
    (status : success = true → error = 0) (closeSuccess : Bool) (closeError : Nat)
    (closeStatus : closeSuccess = true → closeError = 0) (script rest : Term) :
    sync_directory (initial state (opening
      (outcome "sync_dir" success error (outcome "close_dir" closeSuccess closeError script)) rest)) =
      (.ok (if success then .Ok () else .Err ⟨error⟩),world state success true script rest) := by
  simp only [sync_directory,monadLift_self]
  rw [open_next]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,NativeM.monadLift_eq,
    NativeM.fromRust_ok,Result.ok_bind]
  rw [sync_next state success error status]
  rw [drop_next state success closeSuccess closeError closeStatus]
  simp [NativeM.ok,Result.ok_apply]

/-- An opening error propagates without allocating or synchronizing anything. -/
theorem opening_error (state : State) (error : Nat) (rest : Term) :
    sync_directory (initial state (.cons (.tuple #[.atom "open",.bitstring directoryName 0,
      .atom "error",.integer error,.nil]) rest)) =
      (.ok (.Err ⟨error⟩),initial state rest) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  have poll : pollOpenReadOnly (toStr ".")
      (initial state (.cons (.tuple #[.atom "open",.bitstring directoryName 0,
        .atom "error",.integer error,.nil]) rest)) =
      some (.ok (.Err ⟨error⟩),initial state rest) := by
    simp [pollOpenReadOnly,supportedOpenPath,directory_bytes,directoryName,initial,ns,names,
      namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,file_name,openChoice,
      pathChoice,replaceNamespaceScript,node,namespaceTypeName,nonnegative]
  simp only [sync_directory,monadLift_self,io_core.open_readonly,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,NativeM.monadLift_eq,
    NativeM.fromRust_ok,Result.ok_apply,NativeM.ok,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

/-- Merely closing the directory never establishes the sync checkpoint. -/
theorem close_directory_contract (state : State) (success : Bool) (error : Nat)
    (status : success = true → error = 0) (script rest : Term) :
    close_directory (initial state (opening (outcome "close_dir" success error script) rest)) =
      (.ok (.Ok ()),world state false true script rest) := by
  simp only [close_directory,monadLift_self]
  rw [open_next]
  simp only [core.result.Result.Insts.CoreOpsTry.branch,NativeM.monadLift_eq,
    NativeM.fromRust_ok,Result.ok_bind]
  rw [drop_next state false success error status]
  simp [NativeM.ok,Result.ok_apply]

/-- The consumed directory capability grants no further file or sync operations. -/
theorem retired_directory (state : State) (committed : Bool) (script rest : Term) :
    directoryHandle ⟨2⟩ (world state committed true script rest) = none ∧
    pollSync ⟨2⟩ (world state committed true script rest) =
      some (.error .exhausted,world state committed true script rest) ∧
    pollClose ⟨2⟩ (world state committed true script rest) =
      some (.error .exhausted,world state committed true script rest) := by
  simp [directoryHandle,pollSync,pollClose,lookup,pollDirectorySync,pollDirectoryClose,
    world,node,typeName,handleTypeName,writableHandleTypeName,
    directoryTypeName,closedDirectoryTypeName]

/-- The directory checkpoint advances on successful sync without modifying the
file's visible/durable byte images. It does not replace a file fsync. -/
theorem directory_checkpoint (state : State) (script rest : Term) :
    sync_directory (initial state (opening
      (outcome "sync_dir" true 0 (outcome "close_dir" true 0 script)) rest)) =
      (.ok (.Ok ()),world state true true script rest) ∧
    (namespaceSnapshot (world state true true script rest)).map (·.committed) = some names ∧
    (world state true true script rest).nativeHeap.filter (fun cell => cell.1 == 1) = [node state] := by
  refine ⟨sync_directory_contract state true 0 (by simp) true 0 (by simp) script rest, ?_, ?_⟩
  · simp [namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,world,ns,
      names,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,file_name,
      node,namespaceTypeName]
  · simp [world,node]

end Directory.Properties
