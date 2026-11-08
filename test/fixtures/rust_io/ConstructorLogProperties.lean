module
public import Record.SharedLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConstructorLogProperties
open NativeFile

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

@[expose] def fileName : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩
@[expose] def directoryName : ByteArray := ⟨#[46]⟩
@[expose] def names : Names := [(fileName,1)]
@[expose] def actionOk (operation : String) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer 0,.bitstring ByteArray.empty 0]) rest
@[expose] def directoryScript : Term := actionOk "sync_dir" (actionOk "close_dir" .nil)
@[expose] def opening : Term :=
  .cons (.tuple #[.atom "open",.bitstring directoryName 0,.atom "ok",.integer 0,directoryScript]) .nil
@[expose] def creating (fileScript : Term) : Term :=
  .cons (.tuple #[.atom "create_new",.bitstring fileName 0,.atom "ok",.integer 0,fileScript]) opening
@[expose] def initial (env : Environment) (fileScript : Term) : Environment :=
  {env with nativeRefCounter := 0, nativeHeap := [(0,namespaceTypeName,encodeNamespace ⟨[],[],[],creating fileScript⟩)]}
@[expose] def fileCells (fileScript : Term) : List (Nat × String × Term) := [
  (2,writableHandleTypeName,encodeHandle ⟨1,0,fileScript⟩),
  (1,inodeTypeName,encode ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩)]
@[expose] def fileReady (env : Environment) (fileScript : Term) : Environment :=
  {env with nativeRefCounter := 2, nativeHeap := fileCells fileScript ++
    [(0,namespaceTypeName,encodeNamespace ⟨names,[],[names],opening⟩)]}
@[expose] def directory (env : Environment) (fileScript : Term) (committed closed : Bool) (script : Term) : Environment :=
  {env with nativeRefCounter := 3, nativeHeap :=
    (3,if closed then closedDirectoryTypeName else directoryTypeName,.tuple #[script]) ::
    fileCells fileScript ++ [(0,namespaceTypeName,encodeNamespace
      ⟨names,if committed then names else [],if committed then [] else [names],.nil⟩)]}
@[expose] def payload : shared_log.LogResource := ⟨⟨4⟩⟩
@[expose] def mutexReady (env : Environment) (fileScript : Term) : Environment :=
  let closed := directory env fileScript true true .nil
  {closed with nativeRefCounter := 4, nativeHeap :=
    (4,NativeMutex.typeName NativeFile,.tuple #[.atom "unlocked",.atom "unpoisoned",.nativeReference 2]) :: closed.nativeHeap}
@[expose] def constructed (env : Environment) (fileScript : Term) : Environment :=
  let mutex := mutexReady env fileScript
  {mutex with nativeRefCounter := 8, nativeHeap := NativeResourceArc.vmCells payload 5 7 8 ++ mutex.nativeHeap}

theorem journal_bytes : bytes (toStr "journal") = fileName := by
  simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,fileName]
  decide +kernel

theorem directory_bytes : bytes (toStr ".") = directoryName := by
  simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,directoryName]
  exact ⟨46, by decide +kernel, by decide +kernel⟩

@[simp] theorem valid_fileName : supportedPath fileName = true := by decide +kernel

theorem create_poll (env : Environment) (script : Term) :
    pollCreateNew (toStr "journal") (initial env script) = some (.ok (.Ok ⟨2⟩),fileReady env script) := by
  simp [pollCreateNew,journal_bytes,initial,creating,opening,pathChoice,valid_fileName,
    namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,encodeNamespace,
    encodeNames,storeNamespace,fileReady,fileCells,names,namespaceTypeName,writableHandleTypeName,
    inodeTypeName,encodeHandle]

theorem open_poll (env : Environment) (script : Term) :
    pollOpenReadOnly (toStr ".") (fileReady env script) =
      some (.ok (.Ok ⟨3⟩),directory env script false false directoryScript) := by
  simp [pollOpenReadOnly,directory_bytes,supportedOpenPath,fileReady,fileCells,opening,openChoice,pathChoice,
    directory,namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    tablesEqual,encodeNamespace,encodeNames,replaceNamespaceScript,names,List.eraseDups_cons,
    valid_fileName,directoryName,namespaceTypeName,directoryTypeName]

theorem sync_poll (env : Environment) (script : Term) :
    pollSync ⟨3⟩ (directory env script false false directoryScript) =
      some (.ok (.Ok ()),directory env script true false (actionOk "close_dir" .nil)) := by
  simp [pollSync,lookup,pollDirectorySync,directoryHandle,directory,directoryScript,actionOk,
    fileCells,action,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,
    encodeNamespace,encodeNames,names,List.eraseDups_cons,valid_fileName,
    storeDirectory,storeNamespace,namespaceTypeName,directoryTypeName,typeName,handleTypeName,writableHandleTypeName]

theorem close_poll (env : Environment) (script : Term) :
    pollClose ⟨3⟩ (directory env script true false (actionOk "close_dir" .nil)) =
      some (.ok (),directory env script true true .nil) := by
  simp [pollClose,lookup,pollDirectoryClose,directoryHandle,directory,actionOk,fileCells,action,
    storeDirectory,typeName,handleTypeName,writableHandleTypeName,directoryTypeName,closedDirectoryTypeName]

/-- The actual three-crate constructor creates the inode/capability, synchronizes
and closes its directory, and allocates the mutex before constructing the Arc. -/
theorem constructor_prefix (env : Environment) (script : Term) :
    Result.ReadyPrefix __CREATE__ (initial env script) (NativeResourceArc.newOwned payload) (mutexReady env script) := by
  simp only [__CREATE__,shared_log.create,create_fresh,io_core.create_new_file,
    monadLift_self,bind_assoc,NativeFile.createNew,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok (⟨2⟩ : NativeFile))) _ (fileReady env script) _ _ (create_poll env script) ?_
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,NativeM.monadLift_eq,
    NativeM.fromRust_ok,sync_directory,io_core.open_readonly,monadLift_self,bind_assoc,
    openReadOnly,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok (⟨3⟩ : NativeFile))) _
    (directory env script false false directoryScript) _ _ (open_poll env script) ?_
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,NativeM.monadLift_eq,
    NativeM.fromRust_ok,io_core.synchronize,monadLift_self,bind_assoc,syncAll,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (directory env script true false (actionOk "close_dir" .nil)) _ _
    (sync_poll env script) ?_
  simp only [Result.ok_bind,NativeOwnedDrop.drop,NativeFile.close,Result.wait_bind]
  refine .wait _ _ (.ok ()) _ (directory env script true true .nil) _ _ (close_poll env script) ?_
  simp only [Result.ok_bind,NativeM.ok,NativeMutex.new,NativeM.allocate,Result.wait_bind]
  refine .wait _ _ (.ok 4 : Except Exception Nat) _ (mutexReady env script) _ _ ?_ ?_
  · simp [directory,fileCells,mutexReady]
  · simpa [Result.ofExcept,NativeM.ok,NativeM.expectOk_ok,Result.bind_ok,payload,mutexReady,directory,fileCells] using
      (Result.ReadyPrefix.refl (NativeResourceArc.newOwned payload) (mutexReady env script))

/-- Constructor-owned cells are below the next Arc allocation; none is a
pre-existing owner or VM term of that fresh allocation. -/
theorem frame_below (env : Environment) (script : Term) :
    NativeResourceArc.FrameBelow shared_log.LogResource 4 (mutexReady env script).nativeHeap := by
  intro cell member
  simp only [mutexReady,directory,fileCells,List.cons_append,List.nil_append,List.mem_cons,
    List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp [NativeResourceArc.handleType,NativeResourceArc.termType,NativeMutex.typeName,
      closedDirectoryTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

/-- The returned term retains exactly one VM pin for the constructed payload. -/
theorem pinned (env : Environment) (script : Term) :
    NativeResourceArc.Pinned payload 5 7 8 (constructed env script) := by
  constructor
  · simp [constructed,mutexReady]
  · intro cell member
    simp only [constructed,mutexReady,directory,fileCells,NativeResourceArc.vmCells,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [constructed,mutexReady]
  all_goals simp [constructed,mutexReady,directory,fileCells,NativeResourceArc.vmCells,
    NativeResourceArc.handleType,NativeResourceArc.termType,closedDirectoryTypeName,
    writableHandleTypeName,inodeTypeName,namespaceTypeName]

end Record.ConstructorLogProperties
