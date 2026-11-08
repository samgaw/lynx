module
public import FileResource.DirectoryFailure
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.FailurePhases
open NativeFile FileResource.CreatedCalls FileResource.Creation
open DirectoryFailure (Failure)

/-- Indexed constructors exclude directory-operation boundaries which cannot be
reached when directory opening failed. -/
inductive Boundary : Failure → Type where
  | beforeDecode {failure : Failure} : Boundary failure
  | beforeFileSync {failure : Failure} : Boundary failure
  | beforeOpen {failure : Failure} : Boundary failure
  | beforeSync : Boundary .synchronization
  | beforeClose : Boundary .synchronization
  | beforeRelease {failure : Failure} : Boundary failure
  | beforeErrorDrop {failure : Failure} : Boundary failure
  | returned {failure : Failure} : Boundary failure

private inductive Point where
  | beforeDecode | beforeFileSync | beforeOpen | beforeSync | beforeClose
  | beforeRelease | beforeErrorDrop | returned

private def toPoint {failure : Failure} : Boundary failure → Point
  | .beforeDecode => .beforeDecode
  | .beforeFileSync => .beforeFileSync
  | .beforeOpen => .beforeOpen
  | .beforeSync => .beforeSync
  | .beforeClose => .beforeClose
  | .beforeRelease => .beforeRelease
  | .beforeErrorDrop => .beforeErrorDrop
  | .returned => .returned

private def pointEnv (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) : Point → Environment
  | .beforeDecode => DirectoryFailure.initial env value failure closeFailed
  | .beforeFileSync => DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed)
  | .beforeOpen => DirectoryFailure.owned env (Record.synced value) (DirectoryFailure.namespaceBefore failure closeFailed)
  | .beforeSync => DirectoryFailure.directory env value false (DirectoryFailure.syncing closeFailed)
  | .beforeClose => DirectoryFailure.directory env value false (DirectoryFailure.closing closeFailed)
  | .beforeRelease => DirectoryFailure.nativeDone env value failure
  | .beforeErrorDrop => DirectoryFailure.released env value failure
  | .returned => DirectoryFailure.done env value failure

@[expose] def boundaryEnv (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure) : Environment :=
  match boundary with
  | .beforeDecode => DirectoryFailure.initial env value failure closeFailed
  | .beforeFileSync => DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed)
  | .beforeOpen => DirectoryFailure.owned env (Record.synced value) (DirectoryFailure.namespaceBefore failure closeFailed)
  | .beforeSync => DirectoryFailure.directory env value false (DirectoryFailure.syncing closeFailed)
  | .beforeClose => DirectoryFailure.directory env value false (DirectoryFailure.closing closeFailed)
  | .beforeRelease => DirectoryFailure.nativeDone env value failure
  | .beforeErrorDrop => DirectoryFailure.released env value failure
  | .returned => DirectoryFailure.done env value failure

/-- Actual successful file synchronization, stopping before directory opening. -/
theorem open_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) :
    Result.ReadyPrefix (file_resource_commit ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed))
      effects_core.synchronize_directory
      (DirectoryFailure.owned env (Record.synced value) (DirectoryFailure.namespaceBefore failure closeFailed)) := by
  simp only [file_resource_commit,file_resource_sync,monadLift_self,bind_assoc]
  apply ((DirectoryFailure.borrow_prefix env (Record.written value)
    (DirectoryFailure.namespaceBefore failure closeFailed)).bind _).trans
  simp only [Result.ok_bind,payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _
    (DirectoryFailure.file_poll env value (DirectoryFailure.namespaceBefore failure closeFailed))
  simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  exact .refl _ _

/-- Opening succeeded; the actual Rust residual still contains fsync and drop. -/
theorem sync_prefix (env : Environment) (value : U16) (closeFailed : Bool) :
    Result.ReadyPrefix (file_resource_commit ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore .synchronization closeFailed))
      (do
        let result ← syncAll ⟨12⟩
        NativeOwnedDrop.drop (⟨12⟩ : NativeFile)
        NativeM.ok result) (DirectoryFailure.directory env value false (DirectoryFailure.syncing closeFailed)) := by
  apply (open_prefix env value .synchronization closeFailed).trans
  simp only [effects_core.synchronize_directory,monadLift_self,openReadOnly,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (DirectoryFailure.open_sync_poll env value closeFailed)
  simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  exact .refl _ _

/-- Directory fsync failed, but the compiler-owned directory destructor remains
in the actual continuation. Its close outcome is not silently skipped. -/
theorem close_prefix (env : Environment) (value : U16) (closeFailed : Bool) :
    Result.ReadyPrefix (file_resource_commit ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore .synchronization closeFailed))
      (do
        NativeOwnedDrop.drop (⟨12⟩ : NativeFile)
        NativeM.ok (.Err ⟨10⟩)) (DirectoryFailure.directory env value false (DirectoryFailure.closing closeFailed)) := by
  apply (sync_prefix env value closeFailed).trans
  simp only [syncAll,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (DirectoryFailure.directory_sync_poll env value closeFailed)
  simp only [Result.ok_bind]
  exact .refl _ _

private def finish (outcome : core.result.Result Unit NativeIoError) : NativeM Bool := do
  file_resource_release ⟨3,11⟩
  match outcome with
  | .Ok _ => NativeM.ok true
  | .Err error => do
    NativeOwnedDrop.drop error
    NativeM.ok false

private theorem compiled : __COMMIT__ ⟨3,11⟩ = file_resource_commit ⟨3,11⟩ >>= finish := rfl

private theorem lift_commit (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (remaining : NativeM (core.result.Result Unit NativeIoError)) (after : Environment)
    (trace : Result.ReadyPrefix (file_resource_commit ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed))
      remaining after) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed))
      (remaining >>= finish) after := by
  rw [compiled]
  exact trace.bind finish

/-- The Rust resource owner has been released, while disposal of the admitted
OS error is still actual residual work. The VM pin remains independent. -/
theorem released_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed))
      (do
        NativeOwnedDrop.drop (⟨10⟩ : NativeIoError)
        NativeM.ok false) (DirectoryFailure.released env value failure) := by
  simp only [__COMMIT__,monadLift_self]
  apply ((DirectoryFailure.commit_prefix env value failure closeFailed).bind _).trans
  simp only [Result.ok_bind]
  apply ((DirectoryFailure.release_prefix env value failure).bind _).trans
  simp only [Result.ok_bind]
  exact .refl _ _

private theorem lift_decode (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (remaining : NativeM Bool) (after : Environment)
    (trace : Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩)
      (DirectoryFailure.owned env (Record.written value) (DirectoryFailure.namespaceBefore failure closeFailed))
      remaining after) :
    ∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (DirectoryFailure.initial env value failure closeFailed) residual after := by
  refine ⟨Rustler.executeNative remaining Rustler.encodeBool,?_⟩
  apply ((DirectoryFailure.decode_prefix env value failure closeFailed registered).bind _).trans
  simpa only [Result.ok_bind] using Rustler.executeNative_readyPrefix trace Rustler.encodeBool

/-- Every legal failure/cleanup boundary is reached by an actual prefix of the
complete decoded Rustler invocation, preserving the remaining Rust computation. -/
theorem boundary_prefix (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    ∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (DirectoryFailure.initial env value failure closeFailed) residual (boundaryEnv env value failure closeFailed boundary) := by
  cases boundary with
  | beforeDecode =>
    refine ⟨(do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool),?_⟩
    exact .refl _ _
  | beforeFileSync =>
    refine ⟨Rustler.executeNative (__COMMIT__ ⟨3,11⟩) Rustler.encodeBool,?_⟩
    simpa only [boundaryEnv,Result.ok_bind] using
      (DirectoryFailure.decode_prefix env value failure closeFailed registered).bind
        (fun owner => Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
  | beforeOpen =>
    exact lift_decode env value failure closeFailed registered _ _
      (lift_commit env value failure closeFailed _ _ (open_prefix env value failure closeFailed))
  | beforeSync =>
    exact lift_decode env value .synchronization closeFailed registered _ _
      (lift_commit env value .synchronization closeFailed _ _ (sync_prefix env value closeFailed))
  | beforeClose =>
    exact lift_decode env value .synchronization closeFailed registered _ _
      (lift_commit env value .synchronization closeFailed _ _ (close_prefix env value closeFailed))
  | beforeRelease =>
    exact lift_decode env value failure closeFailed registered _ _
      (lift_commit env value failure closeFailed _ _ (DirectoryFailure.commit_prefix env value failure closeFailed))
  | beforeErrorDrop =>
    exact lift_decode env value failure closeFailed registered _ _
      (released_prefix env value failure closeFailed)
  | returned => exact ⟨_,DirectoryFailure.call_prefix env value failure closeFailed registered⟩

@[expose] def unflushed {failure : Failure} : Boundary failure → Bool
  | .beforeDecode | .beforeFileSync => true
  | _ => false

@[expose] def boundaryWater (failure : Failure) : Boundary failure → Nat
  | .beforeDecode => 10
  | .beforeFileSync | .beforeOpen => 11
  | .beforeSync | .beforeClose => 12
  | _ => DirectoryFailure.water failure

private def unflushedPoint : Point → Bool
  | .beforeDecode | .beforeFileSync => true
  | _ => false
private def durable (value : U16) (point : Point) : ByteArray :=
  if unflushedPoint point then ByteArray.empty else Record.content value
private def pointWater (failure : Failure) : Point → Nat
  | .beforeDecode => 10
  | .beforeFileSync | .beforeOpen => 11
  | .beforeSync | .beforeClose => 12
  | _ => DirectoryFailure.water failure
private def namespaceScript (failure : Failure) (closeFailed : Bool) : Point → Term
  | .beforeDecode | .beforeFileSync | .beforeOpen => DirectoryFailure.opening failure closeFailed
  | _ => .nil

private theorem boundary_point (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure) :
    boundaryEnv env value failure closeFailed boundary = pointEnv env value failure closeFailed (toPoint boundary) := by
  cases boundary <;> rfl
private theorem unflushed_point {failure : Failure} (boundary : Boundary failure) :
    unflushedPoint (toPoint boundary) = unflushed boundary := by cases boundary <;> rfl
private theorem water_point (failure : Failure) (boundary : Boundary failure) :
    pointWater failure (toPoint boundary) = boundaryWater failure boundary := by cases boundary <;> rfl
private theorem positive_water (failure : Failure) (boundary : Boundary failure) :
    1 ≤ boundaryWater failure boundary := by
  cases failure <;> cases boundary <;> decide +kernel

private theorem namespace_view (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (point : Point) :
    namespaceSnapshot (pointEnv env value failure closeFailed point) =
      some {Publish.namespaceAfter false with script := namespaceScript failure closeFailed point} := by
  cases failure <;> cases point <;>
    simp [pointEnv,namespaceScript,DirectoryFailure.initial,DirectoryFailure.owned,DirectoryFailure.directory,
      DirectoryFailure.nativeDone,DirectoryFailure.released,DirectoryFailure.done,DirectoryFailure.water,
      DirectoryFailure.tombstone,CommitFailure.errorCell,NativeResourceArc.vmCells,frame,DirectoryFailure.namespaceBefore,
      Publish.namespaceAfter,Publish.names,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,Publish.valid_path]

private theorem inode_view (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (point : Point) :
    inode 1 (pointEnv env value failure closeFailed point) =
      some ⟨Record.content value,durable value point,0,.nil⟩ := by
  cases failure <;> cases point <;>
    simp [pointEnv,durable,unflushedPoint,DirectoryFailure.initial,DirectoryFailure.owned,DirectoryFailure.directory,
      DirectoryFailure.nativeDone,DirectoryFailure.released,DirectoryFailure.done,DirectoryFailure.water,
      DirectoryFailure.tombstone,CommitFailure.errorCell,NativeIoError.typeName,NativeResourceArc.vmCells,frame,
      Record.written,Record.synced,inode,decode,encode,limit,Record.content_size,List.filter,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

private theorem inode_cells (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (point : Point) :
    (pointEnv env value failure closeFailed point).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Record.content value,durable value point,0,.nil⟩)] := by
  cases failure <;> cases point <;>
    simp [pointEnv,durable,unflushedPoint,DirectoryFailure.initial,DirectoryFailure.owned,DirectoryFailure.directory,
      DirectoryFailure.nativeDone,DirectoryFailure.released,DirectoryFailure.done,DirectoryFailure.water,
      DirectoryFailure.tombstone,CommitFailure.errorCell,NativeIoError.typeName,NativeResourceArc.vmCells,frame,
      Record.written,Record.synced,NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

private theorem water_view (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (point : Point) :
    (pointEnv env value failure closeFailed point).refCounter = pointWater failure point := by
  cases failure <;> cases point <;> rfl

/-- Classify every admitted image at each actual failure/cleanup boundary.
Before file fsync the fresh record may tear; afterwards its data is fixed.
Directory failure never supplies the name-retention guarantee. -/
theorem boundary_crash (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value failure closeFailed boundary) = some image) :
    ∃ mask contents, masks = [(1,mask)] ∧
      persist (if unflushed boundary then ByteArray.empty else Record.content value) (Record.content value) mask = some contents ∧
      image.inodes = [(1,contents)] ∧ image.highWater = boundaryWater failure boundary ∧
      (image.names = [] ∨ image.names = Publish.names) := by
  have trace := Publish.crash_shape (pointEnv env value failure closeFailed (toPoint boundary))
    ⟨Record.content value,durable value (toPoint boundary),0,.nil⟩ false (namespaceScript failure closeFailed (toPoint boundary))
    (namespace_view env value failure closeFailed (toPoint boundary))
    (inode_cells env value failure closeFailed (toPoint boundary)) (inode_view env value failure closeFailed (toPoint boundary))
    chosen masks image (by simpa only [boundary_point] using accepted)
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names,published⟩ := trace
  refine ⟨mask,contents,masksEq,?_,inodes,?_,names⟩
  · simpa only [durable,unflushed_point] using saved
  · simpa only [water_view,water_point] using water

/-- Every interrupted failed invocation has an actual residual and every
admitted image has a consistent checked Rust recovery: missing-name error,
rejected incomplete/torn record, or exactly the original value. -/
theorem boundary_recovery (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value failure closeFailed boundary) = some image) :
    (∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (DirectoryFailure.initial env value failure closeFailed) residual
      (boundaryEnv env value failure closeFailed boundary)) ∧
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  refine ⟨boundary_prefix env value failure closeFailed boundary registered,?_⟩
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names⟩ :=
    boundary_crash env value failure closeFailed boundary chosen masks image accepted
  have fresh : ∃ selected, persist ByteArray.empty (Record.content value) selected = some contents := by
    by_cases early : unflushed boundary = true
    · exact ⟨mask,by simpa [early] using saved⟩
    · have same := Publish.persist_equal_images (Record.content value) mask contents (by simpa [early] using saved)
      subst contents
      refine ⟨RecordRecovery.tearingMask true true true true,?_⟩
      simpa [RecordRecovery.tornData,Record.selected,RecordRecovery.content_layout] using
        RecordRecovery.persist_torn value true true true true
  obtain ⟨selected,persisted⟩ := fresh
  have bound := ShortRecovery.fresh_image_size value selected contents persisted
  have valid := positive_water failure boundary
  rcases names with absent | retained
  · have imageEq : image = ⟨[],[(1,contents)],boundaryWater failure boundary⟩ := by cases image; simp_all
    refine ⟨ShortRecovery.missingChoice error,ShortRecovery.missingBoot contents (boundaryWater failure boundary) error,
      ShortRecovery.missingDone contents (boundaryWater failure boundary),.Err ⟨error⟩,?_,
      ShortRecovery.missing_recovery contents (boundaryWater failure boundary) error,Or.inl rfl⟩
    rw [imageEq]
    exact ShortRecovery.missing_restart contents (by simp only [limit]; omega) _ valid error
  · have imageEq : image = ⟨Publish.names,[(1,contents)],boundaryWater failure boundary⟩ := by cases image; simp_all
    obtain ⟨script,before,after,result,restarted,recovered,allowed⟩ :=
      ShortRecovery.persisted_image_recovery value selected contents persisted _ valid
    refine ⟨script,before,after,.Ok result,?_,recovered,Or.inr ?_⟩
    · rw [imageEq]; exact restarted
    · rcases allowed with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- After successful file fsync, any retained-name image at a later failure or
cleanup boundary recovers exactly the original value, despite the failed call. -/
theorem post_sync_recovery (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure) (synced : unflushed boundary = false)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (retained : image.names = Publish.names)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value failure closeFailed boundary) = some image) :
    restartFilesystem image RecordRecovery.openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) (boundaryWater failure boundary)) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) (boundaryWater failure boundary)) =
      (.ok (.Ok (some value)),RecordRecovery.scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) (boundaryWater failure boundary) 4 .nil true) := by
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names⟩ :=
    boundary_crash env value failure closeFailed boundary chosen masks image accepted
  have same := Publish.persist_equal_images (Record.content value) mask contents (by simpa [synced] using saved)
  subst contents
  have imageEq : image = ⟨Publish.names,[(1,Record.content value)],boundaryWater failure boundary⟩ := by cases image; simp_all
  have valid := positive_water failure boundary
  refine ⟨?_,RecordRecovery.recover_value value _ valid⟩
  rw [imageEq,RecordRecovery.content_layout]
  exact RecordRecovery.restart_image _ _ _ _ _ valid

private theorem full_bytes (value : U16) (point : Point) :
    persist (durable value point) (Record.content value) (RecordRecovery.tearingMask true true true true) =
      some (Record.content value) := by
  by_cases early : unflushedPoint point = true
  · simpa [durable,early,RecordRecovery.tornData,Record.selected,RecordRecovery.content_layout] using
      RecordRecovery.persist_torn value true true true true
  · simp only [durable,early]
    rw [RecordRecovery.content_layout]
    rfl

/-- Both retained-name and lost-name images are concrete at every legal
failure/cleanup boundary. Prefix and image hypotheses are therefore inhabited. -/
theorem boundary_witness (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure) (retainName : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (DirectoryFailure.initial env value failure closeFailed) residual
      (boundaryEnv env value failure closeFailed boundary)) ∧
    filesystemCrashImage (if retainName then Publish.names else [])
      [(1,RecordRecovery.tearingMask true true true true)] (boundaryEnv env value failure closeFailed boundary) =
      some ⟨(if retainName then Publish.names else []),[(1,Record.content value)],boundaryWater failure boundary⟩ := by
  refine ⟨boundary_prefix env value failure closeFailed boundary registered,?_⟩
  rw [boundary_point]
  simp only [filesystemCrashImage,namespace_view,inode_cells,Bind.bind,Option.bind_some]
  cases retainName <;>
    simp [Publish.namespaceAfter,Publish.names,namespaceTable,namespaceEntry,encodeNames,List.eraseDups_cons,
      namespaceCrashAllowed,namedInode,Publish.valid_path,inode_view,full_bytes,Bind.bind,water_view,water_point]

/-- A retained, fully synchronized image from an interrupted failed call also
composes with every finite supported mixed recovery-error/crash trace. This is
conditional recovery safety, not an acknowledgment or infinite-failure liveness. -/
theorem post_sync_attempts (env : Environment) (value : U16) (failure : Failure) (closeFailed : Bool)
    (boundary : Boundary failure) (synced : unflushed boundary = false)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
    (retained : image.names = Publish.names)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value failure closeFailed boundary) = some image)
    (trace : RecordErrors.Attempts value image.highWater last) :
    (∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (DirectoryFailure.initial env value failure closeFailed) residual
      (boundaryEnv env value failure closeFailed boundary)) ∧
    restartFilesystem image RecordRecovery.openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) last) =
      (.ok (.Ok (some value)),RecordRecovery.scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last 4 .nil true) := by
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names⟩ :=
    boundary_crash env value failure closeFailed boundary chosen masks image accepted
  have valid : 1 ≤ image.highWater := by rw [water]; exact positive_water failure boundary
  have restarted := (post_sync_recovery env value failure closeFailed boundary synced chosen masks image retained accepted).1
  refine ⟨boundary_prefix env value failure closeFailed boundary registered,?_,
    (RecordErrors.finite_attempts value image.highWater last trace valid).2.2⟩
  simpa only [water] using restarted

end FileResource.FailurePhases
