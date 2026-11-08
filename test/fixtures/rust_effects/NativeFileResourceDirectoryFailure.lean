module
public import FileResource.CommitFailure
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.DirectoryFailure
open NativeFile FileResource.CreatedCalls FileResource.Creation

inductive Failure where
  | opening
  | synchronization
  deriving DecidableEq

@[expose] def closing (failed : Bool) : Term :=
  .cons (.tuple #[.atom "close_dir",.atom (if failed then "error" else "ok"),
    .integer (if failed then 42 else 0),.bitstring ByteArray.empty 0]) .nil
@[expose] def syncing (closeFailed : Bool) : Term :=
  .cons (.tuple #[.atom "sync_dir",.atom "error",.integer 10,.bitstring ByteArray.empty 0]) (closing closeFailed)
@[expose] def opening (failure : Failure) (closeFailed : Bool) : Term :=
  .cons (.tuple #[.atom "open",.bitstring ⟨#[46]⟩ 0,
    .atom (match failure with | .opening => "error" | .synchronization => "ok"),
    .integer (match failure with | .opening => 10 | .synchronization => 0),
    (match failure with | .opening => .nil | .synchronization => syncing closeFailed)]) .nil
@[expose] def namespaceBefore (failure : Failure) (closeFailed : Bool) : NamespaceSnapshot :=
  ⟨Publish.names,[],[Publish.names],opening failure closeFailed⟩

/-- The unique callback-free OS error is host-admitted, as in the file-fsync
failure proof. Native error allocation and reclamation remain trusted. -/
@[expose] def initial (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) : Environment :=
  {env with refCounter := 10,nativeHeap := CommitFailure.errorCell ::
    NativeResourceArc.vmCells payload 3 5 6 ++ frame (Record.written value) (namespaceBefore failure closeFailed)}
@[expose] def owned (env : Environment) (state : State) (ns : NamespaceSnapshot) : Environment :=
  {env with refCounter := 11,nativeHeap := [
    (11,NativeResourceArc.handleType effects_native.FileResource,.reference 3),CommitFailure.errorCell,
    (6,NativeResourceArc.termType effects_native.FileResource,.tuple #[.reference 3,.reference 5]),
    (5,NativeResourceArc.handleType effects_native.FileResource,.reference 3),
    (3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])]
      ++ frame state ns}
@[expose] def directory (env : Environment) (value : U16) (closed : Bool) (script : Term) : Environment :=
  {owned env (Record.synced value) (Publish.namespaceAfter false) with
    refCounter := 12
    nativeHeap := (12,(if closed then closedDirectoryTypeName else directoryTypeName),.tuple #[script]) ::
      (owned env (Record.synced value) (Publish.namespaceAfter false)).nativeHeap}
@[expose] def nativeDone (env : Environment) (value : U16) : Failure → Environment
  | .opening => owned env (Record.synced value) (Publish.namespaceAfter false)
  | .synchronization => directory env value true .nil
@[expose] def water : Failure → Nat | .opening => 11 | .synchronization => 12
@[expose] def tombstone : Failure → List (Nat × String × Term)
  | .opening => []
  | .synchronization => [(12,closedDirectoryTypeName,.tuple #[.nil])]
@[expose] def released (env : Environment) (value : U16) (failure : Failure) : Environment :=
  {env with refCounter := water failure,nativeHeap := tombstone failure ++ CommitFailure.errorCell ::
    NativeResourceArc.vmCells payload 3 5 6 ++ frame (Record.synced value) (Publish.namespaceAfter false)}
@[expose] def done (env : Environment) (value : U16) (failure : Failure) : Environment :=
  {env with refCounter := water failure,nativeHeap := tombstone failure ++
    NativeResourceArc.vmCells payload 3 5 6 ++ frame (Record.synced value) (Publish.namespaceAfter false)}

private theorem pinned (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) :
    NativeResourceArc.Pinned payload 3 5 6 (initial env value failure closeFailed) := by
  constructor
  · simp [initial]
  · intro cell member
    simp only [initial,CommitFailure.errorCell,NativeResourceArc.vmCells,frame,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [initial]
  · simp [initial,CommitFailure.errorCell,NativeResourceArc.vmCells,frame]
  · simp [initial,CommitFailure.errorCell,NativeResourceArc.vmCells,frame]
  · simp [initial,CommitFailure.errorCell,NativeResourceArc.vmCells,frame]
  · simp [initial,CommitFailure.errorCell,NativeResourceArc.vmCells,frame,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      NativeIoError.typeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem decode_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.reference 6)) (initial env value failure closeFailed)
      (.ok (⟨3,11⟩ : NativeResourceArc effects_native.FileResource))
      (owned env (Record.written value) (namespaceBefore failure closeFailed)) := by
  simpa [initial,owned,NativeResourceArc.vmCells,frame,CommitFailure.errorCell,List.map] using
    NativeResourceArc.decode_pinned_prefix payload (initial env value failure closeFailed) 3 5 6
      (pinned env value failure closeFailed) registered

private theorem borrowed (env : Environment) (state : State) (ns : NamespaceSnapshot) :
    Result.ReadyPrefix (NativeResourceArc.deref (⟨3,11⟩ : NativeResourceArc effects_native.FileResource))
      (owned env state ns) (.ok payload) (owned env state ns) := by
  apply NativeResourceArc.deref_retained_prefix
  all_goals simp [owned,CommitFailure.errorCell,frame,List.filter,NativeIoError.typeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem file_poll (env : Environment) (value : U16) (ns : NamespaceSnapshot) :
    pollSync ⟨2⟩ (owned env (Record.written value) ns) =
      some (.ok (.Ok ()),owned env (Record.synced value) ns) := by
  simp [pollSync,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,owned,frame,CommitFailure.errorCell,
    inode,decode,encode,limit,Record.content_size,blocked,Record.written,Record.synced,syncStep,syncChoice,action,
    store,sharedStore,List.filter,List.map,NativeIoError.typeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName,typeName,handleTypeName]

theorem open_error_poll (env : Environment) (value : U16) (closeFailed : Bool) :
    pollOpenReadOnly (toStr ".") (owned env (Record.synced value) (namespaceBefore .opening closeFailed)) =
      some (.ok (.Err ⟨10⟩),nativeDone env value .opening) := by
  simp [pollOpenReadOnly,Publish.dot_bytes,supportedOpenPath,owned,frame,CommitFailure.errorCell,
    namespaceBefore,opening,Publish.namespaceAfter,Publish.names,namespaceState,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    Publish.valid_path,openChoice,pathChoice,replaceNamespaceScript,nativeDone]

theorem open_sync_poll (env : Environment) (value : U16) (closeFailed : Bool) :
    pollOpenReadOnly (toStr ".") (owned env (Record.synced value) (namespaceBefore .synchronization closeFailed)) =
      some (.ok (.Ok ⟨12⟩),directory env value false (syncing closeFailed)) := by
  simp [pollOpenReadOnly,Publish.dot_bytes,supportedOpenPath,owned,directory,frame,CommitFailure.errorCell,
    namespaceBefore,opening,Publish.namespaceAfter,Publish.names,namespaceState,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    Publish.valid_path,openChoice,pathChoice,replaceNamespaceScript]

theorem directory_sync_poll (env : Environment) (value : U16) (closeFailed : Bool) :
    pollSync ⟨12⟩ (directory env value false (syncing closeFailed)) =
      some (.ok (.Err ⟨10⟩),directory env value false (closing closeFailed)) := by
  simp [pollSync,lookup,pollDirectorySync,directoryHandle,directory,owned,frame,CommitFailure.errorCell,
    Publish.namespaceAfter,Publish.names,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,Publish.valid_path,syncing,action,storeDirectory,
    NativeIoError.typeName,NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    typeName,handleTypeName,writableHandleTypeName,directoryTypeName]

/-- Compiler-owned directory destruction consumes the descriptor on either
admitted close outcome; neither outcome acknowledges namespace durability. -/
theorem directory_close_poll (env : Environment) (value : U16) (closeFailed : Bool) :
    pollClose ⟨12⟩ (directory env value false (closing closeFailed)) =
      some (.ok (),nativeDone env value .synchronization) := by
  cases closeFailed <;>
    simp [pollClose,lookup,pollDirectoryClose,directoryHandle,directory,owned,nativeDone,frame,CommitFailure.errorCell,
      closing,action,storeDirectory,NativeIoError.typeName,NativeResourceArc.typeName,NativeResourceArc.handleType,
      NativeResourceArc.termType,typeName,handleTypeName,writableHandleTypeName,directoryTypeName]

/-- The actual first-party directory helper propagates opening or fsync errors,
including compiler destruction of a successfully opened directory. -/
theorem directory_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) :
    Result.ReadyPrefix effects_core.synchronize_directory
      (owned env (Record.synced value) (namespaceBefore failure closeFailed)) (.ok (.Err ⟨10⟩))
      (nativeDone env value failure) := by
  simp only [effects_core.synchronize_directory,monadLift_self,openReadOnly,Result.wait_bind]
  cases failure
  · apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (open_error_poll env value closeFailed)
    simp [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      NativeM.monadLift_eq,NativeM.fromRust]
    exact .refl _ _
  · apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (open_sync_poll env value closeFailed)
    simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
      core.result.Result.Insts.CoreOpsTry.branch,syncAll,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (directory_sync_poll env value closeFailed)
    simp only [Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
    apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (directory_close_poll env value closeFailed)
    simp only [Result.ok_bind,NativeM.ok]
    exact .refl _ _

/-- Data fsync succeeds before the actual cross-crate directory failure. -/
theorem commit_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) :
    Result.ReadyPrefix (file_resource_commit ⟨3,11⟩)
      (owned env (Record.written value) (namespaceBefore failure closeFailed)) (.ok (.Err ⟨10⟩))
      (nativeDone env value failure) := by
  simp only [file_resource_commit,file_resource_sync,monadLift_self,bind_assoc]
  apply ((borrowed env (Record.written value) (namespaceBefore failure closeFailed)).bind _).trans
  simp only [Result.ok_bind,payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (file_poll env value (namespaceBefore failure closeFailed))
  simpa [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch] using directory_prefix env value failure closeFailed

/-- The failed commit releases only its decoded Rust owner. The originating VM
pin and the synchronized file remain live; an opened directory is already closed. -/
theorem release_prefix (env : Environment) (value : U16) (failure : Failure) :
    Result.ReadyPrefix (file_resource_release ⟨3,11⟩) (nativeDone env value failure) (.ok ())
      (released env value failure) := by
  simp only [file_resource_release,monadLift_self,NativeOwnedDrop.drop]
  apply Result.ReadyPrefix.trans
    (NativeResourceArc.releaseOwned_retained_prefix (⟨3,11⟩ : NativeResourceArc effects_native.FileResource)
      payload (nativeDone env value failure) ?_ ?_ ?_)
  all_goals cases failure <;>
    simp [nativeDone,directory,owned,released,water,tombstone,CommitFailure.errorCell,frame,
      NativeResourceArc.vmCells,List.filter,List.map,NativeIoError.typeName,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,closedDirectoryTypeName]
  all_goals exact .refl _ _

/-- The admitted error is consumed after resource release, without discarding
persistent file data or the closed-directory tombstone. -/
theorem error_prefix (env : Environment) (value : U16) (failure : Failure) :
    Result.ReadyPrefix (NativeOwnedDrop.drop (⟨10⟩ : NativeIoError)) (released env value failure) (.ok ())
      (done env value failure) := by
  simp only [NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability]
  apply Result.ReadyPrefix.get
  cases failure <;>
    simp [released,done,water,tombstone,CommitFailure.errorCell,frame,
      NativeResourceArc.vmCells,List.filter,NativeIoError.typeName]
  all_goals apply Result.ReadyPrefix.set
  all_goals exact .refl _ _

/-- The actual compiled facade returns false for either directory failure,
after completing the compiler-owned cleanup and releasing the native owner. -/
theorem facade_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩)
      (owned env (Record.written value) (namespaceBefore failure closeFailed)) (.ok false)
      (done env value failure) := by
  simp only [__COMMIT__,monadLift_self]
  apply ((commit_prefix env value failure closeFailed).bind _).trans
  simp only [Result.ok_bind]
  apply ((release_prefix env value failure).bind _).trans
  simp only [Result.ok_bind]
  apply ((error_prefix env value failure).bind _).trans
  simp only [Result.ok_bind,NativeM.ok]
  exact .refl _ _

/-- Complete modeled remote invocation, including the actual generated Rustler
facade, resource decoding, native effects, ownership cleanup and result encoding. -/
theorem call_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (initial env value failure closeFailed) (.ok Term.false) (done env value failure) := by
  apply ((decode_prefix env value failure closeFailed registered).bind _).trans
  simp only [Result.ok_bind]
  simpa [Rustler.executeNative,Result.ok_bind,Result.handle,Rustler.encodeBool] using
    Rustler.executeNative_readyPrefix (facade_prefix env value failure closeFailed) Rustler.encodeBool

/-- Ordinary callers observe false, while successful data synchronization and
failed namespace synchronization remain distinct in their terminal environment. -/
theorem call_run (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) (initial env value failure closeFailed) =
      (.ok Term.false,done env value failure) := by
  simpa only [Result.ok_apply] using (call_prefix env value failure closeFailed registered).apply

theorem failure_env {α : Type} (value : U16) (failure : Failure) (closeFailed : Bool)
    (next : Term → Result α) (env : Environment)
    (counter : env.refCounter = 10)
    (heap : env.nativeHeap = CommitFailure.errorCell :: NativeResourceArc.vmCells payload 3 5 6 ++
      frame (Record.written value) (namespaceBefore failure closeFailed))
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      let result ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      next result) env = next Term.false (done env value failure) := by
  have trace := ((call_prefix env value failure closeFailed registered).bind next).apply
  simpa only [Result.ok_bind,initial,← heap,← counter,bind_assoc] using trace

@[expose] def seed (failure : Failure) (closeFailed : Bool) : Environment :=
  initial (({} : Environment).setPdict [(.atom "resource",.reference 6)]) 4660#u16 failure closeFailed
@[simp,expose] def seedOpening : Environment := seed .opening false
@[simp,expose] def seedSynchronization : Environment := seed .synchronization false
@[simp,expose] def seedCloseError : Environment := seed .synchronization true

private theorem namespace_view (env : Environment) (value : U16) (failure : Failure) :
    namespaceSnapshot (done env value failure) = some (Publish.namespaceAfter false) := by
  cases failure <;>
    simp [done,water,tombstone,NativeResourceArc.vmCells,frame,Publish.namespaceAfter,Publish.names,
      namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,
      List.eraseDups_cons,tablesEqual,Publish.valid_path]

private theorem inode_view (env : Environment) (value : U16) (failure : Failure) :
    inode 1 (done env value failure) = some ⟨Record.content value,Record.content value,0,.nil⟩ := by
  cases failure <;>
    simp [done,water,tombstone,NativeResourceArc.vmCells,frame,Record.synced,inode,decode,encode,limit,
      Record.content_size,List.filter,NativeResourceArc.typeName,NativeResourceArc.handleType,
      NativeResourceArc.termType,writableHandleTypeName,inodeTypeName,namespaceTypeName,closedDirectoryTypeName]

private theorem inode_cells (env : Environment) (value : U16) (failure : Failure) :
    (done env value failure).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Record.content value,Record.content value,0,.nil⟩)] := by
  cases failure <;>
    simp [done,water,tombstone,NativeResourceArc.vmCells,frame,Record.synced,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,closedDirectoryTypeName]

/-- Every admitted crash after the failed directory commit retains the fsynced
file bytes, but may lose the unacknowledged directory entry. -/
theorem crash_shape (env : Environment) (value : U16) (failure : Failure) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (done env value failure) = some image) :
    image.inodes = [(1,Record.content value)] ∧ image.highWater = water failure ∧
      (image.names = [] ∨ image.names = Publish.names) := by
  obtain ⟨mask,contents,masksEq,saved,inodes,high,names,published⟩ :=
    Publish.crash_shape (done env value failure)
      ⟨Record.content value,Record.content value,0,.nil⟩ false .nil
      (namespace_view env value failure) (inode_cells env value failure) (inode_view env value failure)
      chosen masks image accepted
  have same := Publish.persist_equal_images (Record.content value) mask contents saved
  subst contents
  exact ⟨inodes,high,names⟩

/-- Actual failed remote invocation composes with every admitted terminal image
and the actual checked Rust recovery. Missing names propagate opening failure;
retained names recover exactly the original synchronized value. -/
theorem failure_recovery (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks (done env value failure) = some image) :
    Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (initial env value failure closeFailed) (.ok Term.false) (done env value failure) ∧
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok (some value)) := by
  refine ⟨call_prefix env value failure closeFailed registered,?_⟩
  obtain ⟨inodes,high,names⟩ := crash_shape env value failure chosen masks image accepted
  have valid : 1 ≤ water failure := by cases failure <;> decide +kernel
  rcases names with absent | retained
  · have imageEq : image = ⟨[],[(1,Record.content value)],water failure⟩ := by cases image; simp_all
    refine ⟨ShortRecovery.missingChoice error,ShortRecovery.missingBoot (Record.content value) (water failure) error,
      ShortRecovery.missingDone (Record.content value) (water failure),.Err ⟨error⟩,?_,
      ShortRecovery.missing_recovery (Record.content value) (water failure) error,Or.inl rfl⟩
    rw [imageEq]
    exact ShortRecovery.missing_restart _ (by simp [Record.content_size,limit]) _ valid error
  · have imageEq : image = ⟨Publish.names,[(1,Record.content value)],water failure⟩ := by cases image; simp_all
    refine ⟨RecordRecovery.openingScript,
      RecordRecovery.boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) (water failure),
      RecordRecovery.scan (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value))
        (water failure) 4 .nil true,.Ok (some value),?_,RecordRecovery.recover_value value _ valid,Or.inr rfl⟩
    rw [imageEq,RecordRecovery.content_layout]
    exact RecordRecovery.restart_image _ _ _ _ _ valid

private theorem full_bytes (value : U16) :
    persist (Record.content value) (Record.content value) (RecordRecovery.tearingMask true true true true) =
      some (Record.content value) := by
  rw [RecordRecovery.content_layout]
  rfl

/-- Each directory failure has an actual false-returning invocation and a
concrete admitted lost-name crash, even when all record bytes are durable. -/
theorem lost_name_witness (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (initial env value failure closeFailed) (.ok Term.false) (done env value failure) ∧
    filesystemCrashImage [] [(1,RecordRecovery.tearingMask true true true true)] (done env value failure) =
      some ⟨[],[(1,Record.content value)],water failure⟩ := by
  refine ⟨call_prefix env value failure closeFailed registered,?_⟩
  simp only [filesystemCrashImage,namespace_view,inode_cells,Bind.bind,Option.bind_some]
  simp [Publish.namespaceAfter,Publish.names,namespaceTable,encodeNames,namespaceCrashAllowed,namedInode,
    inode_view,full_bytes,Bind.bind]
  rfl

end FileResource.DirectoryFailure
