module
public import FileResource.CommitFailure
public import FileResource.Persistence
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.SyncErrorRecovery
open NativeFile FileResource.CreatedCalls FileResource.Creation

inductive Boundary where
  | beforeDecode | beforeFileSync | failed | released | returned

@[expose] def afterFailure : Boundary → Bool
  | .beforeDecode | .beforeFileSync => false
  | _ => true
@[expose] def boundaryWater : Boundary → Nat | .beforeDecode => 10 | _ => 11
@[expose] def boundaryEnv (env : Environment) (value : U16) (mask saved : ByteArray) (rest : Term) : Boundary → Environment
  | .beforeDecode => CommitFailure.initial env (CommitFailure.before value mask rest)
  | .beforeFileSync => CommitFailure.decoded env (CommitFailure.before value mask rest)
  | .failed => CommitFailure.decoded env (CommitFailure.after value saved rest)
  | .released => CommitFailure.released env (CommitFailure.after value saved rest)
  | .returned => CommitFailure.done env (CommitFailure.after value saved rest)

private def finish (outcome : core.result.Result Unit NativeIoError) : NativeM Bool := do
  file_resource_release ⟨3,11⟩
  match outcome with
  | .Ok _ => NativeM.ok true
  | .Err error => do
    NativeOwnedDrop.drop error
    NativeM.ok false
private theorem compiled : __COMMIT__ ⟨3,11⟩ = file_resource_commit ⟨3,11⟩ >>= finish := rfl

/-- The actual facade has received fsync failure but has not yet released its
Rust resource owner or disposed of the admitted OS error. -/
theorem failed_prefix (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩) (CommitFailure.decoded env (CommitFailure.before value mask rest))
      (do
        file_resource_release ⟨3,11⟩
        NativeOwnedDrop.drop (⟨10⟩ : NativeIoError)
        NativeM.ok false) (CommitFailure.decoded env (CommitFailure.after value saved rest)) := by
  rw [compiled]
  simpa only [Result.ok_bind,finish] using (CommitFailure.commit_prefix env value mask saved persisted rest).bind finish

/-- The resource owner is released before actual error disposal, retaining the
VM pin and all persistent effects made by the unsuccessful fsync. -/
theorem released_prefix (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩) (CommitFailure.decoded env (CommitFailure.before value mask rest))
      (do
        NativeOwnedDrop.drop (⟨10⟩ : NativeIoError)
        NativeM.ok false) (CommitFailure.released env (CommitFailure.after value saved rest)) := by
  simp only [__COMMIT__,monadLift_self]
  apply ((CommitFailure.commit_prefix env value mask saved persisted rest).bind _).trans
  simp only [Result.ok_bind]
  apply ((CommitFailure.release_prefix env (CommitFailure.after value saved rest)).bind _).trans
  simp only [Result.ok_bind]
  exact .refl _ _

private theorem lift_decode (env : Environment) (value : U16) (mask : ByteArray) (rest : Term)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (remaining : NativeM Bool) (after : Environment)
    (trace : Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩) (CommitFailure.decoded env (CommitFailure.before value mask rest))
      remaining after) :
    ∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (CommitFailure.initial env (CommitFailure.before value mask rest)) residual after := by
  refine ⟨Rustler.executeNative remaining Rustler.encodeBool,?_⟩
  apply ((CommitFailure.decode_prefix env (CommitFailure.before value mask rest) registered).bind _).trans
  simpa only [Result.ok_bind] using Rustler.executeNative_readyPrefix trace Rustler.encodeBool

theorem boundary_prefix (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    ∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (CommitFailure.initial env (CommitFailure.before value mask rest)) residual (boundaryEnv env value mask saved rest boundary) := by
  cases boundary with
  | beforeDecode =>
    refine ⟨(do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool),?_⟩
    exact .refl _ _
  | beforeFileSync =>
    refine ⟨Rustler.executeNative (__COMMIT__ ⟨3,11⟩) Rustler.encodeBool,?_⟩
    simpa only [boundaryEnv,Result.ok_bind] using
      (CommitFailure.decode_prefix env (CommitFailure.before value mask rest) registered).bind
        (fun owner => Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
  | failed => exact lift_decode env value mask rest registered _ _ (failed_prefix env value mask saved persisted rest)
  | released => exact lift_decode env value mask rest registered _ _ (released_prefix env value mask saved persisted rest)
  | returned => exact ⟨_,CommitFailure.invocation_prefix env value mask saved persisted registered rest⟩

private theorem namespace_view (env : Environment) (value : U16) (mask saved : ByteArray) (rest : Term) (boundary : Boundary) :
    namespaceSnapshot (boundaryEnv env value mask saved rest boundary) = some Publish.namespaceBefore := by
  cases boundary <;>
    simp [boundaryEnv,CommitFailure.initial,CommitFailure.decoded,CommitFailure.released,CommitFailure.done,
      CommitFailure.errorCell,NativeResourceArc.vmCells,frame,Publish.namespaceBefore,Publish.names,
      namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,
      List.eraseDups_cons,tablesEqual,Publish.valid_path]

private theorem inode_view (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary) :
    inode 1 (boundaryEnv env value mask saved rest boundary) =
      some ⟨Record.content value,(if afterFailure boundary then saved else ByteArray.empty),0,.nil⟩ := by
  have bound := ShortRecovery.fresh_image_size value mask saved persisted
  have bounded : ¬ 1048576 < saved.size := by omega
  cases boundary <;>
    simp [boundaryEnv,afterFailure,CommitFailure.initial,CommitFailure.decoded,CommitFailure.released,CommitFailure.done,
      CommitFailure.before,CommitFailure.after,CommitFailure.errorCell,NativeIoError.typeName,NativeResourceArc.vmCells,frame,
      inode,decode,encode,limit,Record.content_size,List.filter,bounded,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName]

private theorem inode_cells (env : Environment) (value : U16) (mask saved : ByteArray) (rest : Term) (boundary : Boundary) :
    (boundaryEnv env value mask saved rest boundary).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Record.content value,(if afterFailure boundary then saved else ByteArray.empty),0,.nil⟩)] := by
  cases boundary <;>
    simp [boundaryEnv,afterFailure,CommitFailure.initial,CommitFailure.decoded,CommitFailure.released,CommitFailure.done,
      CommitFailure.before,CommitFailure.after,CommitFailure.errorCell,NativeIoError.typeName,NativeResourceArc.vmCells,frame,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName]

private theorem water_view (env : Environment) (value : U16) (mask saved : ByteArray) (rest : Term) (boundary : Boundary) :
    (boundaryEnv env value mask saved rest boundary).nativeRefCounter = boundaryWater boundary := by cases boundary <;> rfl

/-- The crash step starts from the actual saved image after failed fsync,
not the empty acquisition image. Additional permitted persistence is retained. -/
theorem boundary_crash (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value mask saved rest boundary) = some image) :
    ∃ later contents, masks = [(1,later)] ∧
      persist (if afterFailure boundary then saved else ByteArray.empty) (Record.content value) later = some contents ∧
      image.inodes = [(1,contents)] ∧ image.highWater = boundaryWater boundary ∧
      (image.names = [] ∨ image.names = Publish.names) := by
  obtain ⟨later,contents,masksEq,step,inodes,water,names,published⟩ :=
    Publish.crash_shape (boundaryEnv env value mask saved rest boundary)
      ⟨Record.content value,(if afterFailure boundary then saved else ByteArray.empty),0,.nil⟩ false Publish.opening
      (namespace_view env value mask saved rest boundary) (inode_cells env value mask saved rest boundary)
      (inode_view env value mask saved persisted rest boundary) chosen masks image accepted
  exact ⟨later,contents,masksEq,step,inodes,by simpa only [water_view] using water,names⟩

/-- Every admitted post-error crash image has a consistent actual Rust recovery,
even when background persistence advanced beyond the failed operation's image. -/
theorem boundary_recovery (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value mask saved rest boundary) = some image) :
    (∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (CommitFailure.initial env (CommitFailure.before value mask rest)) residual (boundaryEnv env value mask saved rest boundary)) ∧
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  refine ⟨boundary_prefix env value mask saved persisted rest boundary registered,?_⟩
  obtain ⟨later,contents,masksEq,step,inodes,water,names⟩ :=
    boundary_crash env value mask saved persisted rest boundary chosen masks image accepted
  have fresh : ∃ combined, persist ByteArray.empty (Record.content value) combined = some contents := by
    by_cases failed : afterFailure boundary = true
    · exact Persistence.compose ByteArray.empty (Record.content value) mask saved later contents persisted
        (by simpa [failed] using step)
    · exact ⟨later,by simpa [failed] using step⟩
  obtain ⟨combined,admitted⟩ := fresh
  have bound := ShortRecovery.fresh_image_size value combined contents admitted
  have valid : 1 ≤ boundaryWater boundary := by cases boundary <;> decide +kernel
  rcases names with absent | retained
  · have imageEq : image = ⟨[],[(1,contents)],boundaryWater boundary⟩ := by cases image; simp_all
    refine ⟨ShortRecovery.missingChoice error,ShortRecovery.missingBoot contents (boundaryWater boundary) error,
      ShortRecovery.missingDone contents (boundaryWater boundary),.Err ⟨error⟩,?_,
      ShortRecovery.missing_recovery contents (boundaryWater boundary) error,Or.inl rfl⟩
    rw [imageEq]
    exact ShortRecovery.missing_restart contents (by simp only [limit]; omega) _ valid error
  · have imageEq : image = ⟨Publish.names,[(1,contents)],boundaryWater boundary⟩ := by cases image; simp_all
    obtain ⟨script,before,after,result,restarted,recovered,allowed⟩ :=
      ShortRecovery.persisted_image_recovery value combined contents admitted _ valid
    refine ⟨script,before,after,.Ok result,?_,recovered,Or.inr ?_⟩
    · rw [imageEq]; exact restarted
    · rcases allowed with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

/-- Every boundary admits both name outcomes and a fully persisted record,
without presuming that failed fsync left durable data unchanged. -/
theorem boundary_witness (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary)
    (retainName : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (CommitFailure.initial env (CommitFailure.before value mask rest)) residual (boundaryEnv env value mask saved rest boundary)) ∧
    filesystemCrashImage (if retainName then Publish.names else [])
      [(1,Persistence.choices (Record.content value) (Record.content value))] (boundaryEnv env value mask saved rest boundary) =
      some ⟨(if retainName then Publish.names else []),[(1,Record.content value)],boundaryWater boundary⟩ := by
  refine ⟨boundary_prefix env value mask saved persisted rest boundary registered,?_⟩
  simp only [filesystemCrashImage,namespace_view,inode_cells,Bind.bind,Option.bind_some]
  cases retainName <;>
    simp [Publish.namespaceBefore,Publish.names,namespaceTable,namespaceEntry,encodeNames,List.eraseDups_cons,
      namespaceCrashAllowed,namedInode,Publish.valid_path,inode_view env value mask saved persisted rest boundary,
      Persistence.visible_image,Bind.bind,water_view]

/-- Construct the actual admitted filesystem image from a specific additional
persistence step, retaining either permitted name outcome. -/
theorem image_of_persist (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary)
    (later contents : ByteArray)
    (step : persist (if afterFailure boundary then saved else ByteArray.empty) (Record.content value) later = some contents)
    (retainName : Bool) :
    filesystemCrashImage (if retainName then Publish.names else []) [(1,later)]
      (boundaryEnv env value mask saved rest boundary) =
      some ⟨(if retainName then Publish.names else []),[(1,contents)],boundaryWater boundary⟩ := by
  simp only [filesystemCrashImage,namespace_view,inode_cells,Bind.bind,Option.bind_some]
  cases retainName <;>
    simp [Publish.namespaceBefore,Publish.names,namespaceTable,namespaceEntry,encodeNames,List.eraseDups_cons,
      namespaceCrashAllowed,namedInode,Publish.valid_path,inode_view env value mask saved persisted rest boundary,
      step,Bind.bind,water_view]

/-- Any finite permitted background persistence history at a failed-call
boundary collapses to an admitted crash and consistent actual Rust recovery.
The visible image is fixed; concurrent writes require separate composition. -/
theorem finite_background_recovery (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) (boundary : Boundary)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (history : List ByteArray) (contents : ByteArray)
    (advanced : Persistence.advance (Record.content value)
      (if afterFailure boundary then saved else ByteArray.empty) history = some contents)
    (retainName : Bool) (error : Nat) :
    (∃ residual, Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
      (CommitFailure.initial env (CommitFailure.before value mask rest)) residual (boundaryEnv env value mask saved rest boundary)) ∧
    ∃ combined script before after result,
      filesystemCrashImage (if retainName then Publish.names else []) [(1,combined)]
        (boundaryEnv env value mask saved rest boundary) =
        some ⟨(if retainName then Publish.names else []),[(1,contents)],boundaryWater boundary⟩ ∧
      restartFilesystem ⟨(if retainName then Publish.names else []),[(1,contents)],boundaryWater boundary⟩ script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  obtain ⟨combined,step⟩ := Persistence.finite_compose
    (if afterFailure boundary then saved else ByteArray.empty) (Record.content value) history contents advanced
  have captured := image_of_persist env value mask saved persisted rest boundary combined contents step retainName
  obtain ⟨front,script,before,after,result,restarted,recovered,allowed⟩ :=
    boundary_recovery env value mask saved persisted rest boundary registered
      (if retainName then Publish.names else []) [(1,combined)]
      ⟨(if retainName then Publish.names else []),[(1,contents)],boundaryWater boundary⟩ error captured
  exact ⟨front,combined,script,before,after,result,captured,restarted,recovered,allowed⟩

end FileResource.SyncErrorRecovery
