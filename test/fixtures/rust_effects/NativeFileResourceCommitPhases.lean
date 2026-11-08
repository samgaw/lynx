module
public import FileResource.RecordCleanup
public import FileResource.ShortRecovery
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.CommitPhases
open NativeFile FileResource.CreatedCalls FileResource.Creation

inductive Phase where
  | beforeFileSync | beforeDirectoryOpen | beforeDirectorySync | beforeDirectoryClose | finished

@[expose] def phaseEnv (env : Environment) (value : U16) : Phase → Environment
  | .beforeFileSync => decodedEnv env (Record.written value) 7 Publish.namespaceBefore
  | .beforeDirectoryOpen => decodedEnv env (Record.synced value) 7 Publish.namespaceBefore
  | .beforeDirectorySync => Publish.directoryEnv env (Record.synced value) 7 false false Publish.syncScript
  | .beforeDirectoryClose => Publish.directoryEnv env (Record.synced value) 7 true false Publish.closeScript
  | .finished => Publish.directoryEnv env (Record.synced value) 7 true true .nil

private theorem borrowed (env : Environment) (value : U16) :
    Result.ReadyPrefix (NativeResourceArc.deref (⟨3,8⟩ : NativeResourceArc effects_native.FileResource))
      (phaseEnv env value .beforeFileSync) (.ok payload) (phaseEnv env value .beforeFileSync) := by
  apply NativeResourceArc.deref_retained_prefix
  all_goals simp [phaseEnv,decodedEnv,frame,List.filter,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName]

private theorem continue_prefix {α β : Type} (body : NativeM α) (value : α) (next : α → NativeM β)
    (before middle after : Environment)
    (trace : Result.ReadyPrefix body before (.ok value) middle)
    (rest : ∃ residual, Result.ReadyPrefix (next value) middle residual after) :
    ∃ residual, Result.ReadyPrefix (body >>= next) before residual after := by
  obtain ⟨residual,following⟩ := rest
  exact ⟨residual,(by simpa only [Result.ok_bind] using (trace.bind next).trans following)⟩

/-- Each phase retains an actual prefix of the extracted Rust resource commit,
including its borrow, data fsync, namespace fsync and directory destructor. -/
theorem phase_prefix (env : Environment) (value : U16) (phase : Phase) :
    ∃ residual, Result.ReadyPrefix (file_resource_commit ⟨3,8⟩)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase) := by
  cases phase
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [file_resource_commit,file_resource_sync,monadLift_self,bind_assoc]
  all_goals apply continue_prefix _ payload _ _ _ _ (borrowed env value)
  all_goals simp only [payload,effects_core.synchronize_file,
    monadLift_self,syncAll,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (file_sync_poll (ns := Publish.namespaceBefore) env (Record.written value) (Record.synced value) 7
      (by decide +kernel) (Record.written_valid value) (Record.written_ready value) (Record.sync_step value))
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch,effects_core.synchronize_directory,
    monadLift_self,openReadOnly,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (Publish.open_poll env (Record.synced value) 7 (by decide +kernel))
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [Result.ok_bind,NativeM.fromRust_ok,
    syncAll,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (Publish.sync_poll env (Record.synced value) 7 (by decide +kernel))
  · exact ⟨_,.refl _ _⟩
  simp only [Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _
    (Publish.close_poll env (Record.synced value) 7 (by decide +kernel))
  exact ⟨_,.refl _ _⟩

/-- Complete the actual Rust commit while retaining the directory destruction
and exact terminal result, so a facade can continue with resource release. -/
theorem complete_prefix (env : Environment) (value : U16) :
    Result.ReadyPrefix (file_resource_commit ⟨3,8⟩) (phaseEnv env value .beforeFileSync)
      (.ok (.Ok ())) (phaseEnv env value .finished) := by
  simp only [file_resource_commit,file_resource_sync,monadLift_self,bind_assoc]
  apply ((borrowed env value).bind _).trans
  simp only [Result.ok_bind,payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _
    (file_sync_poll (ns := Publish.namespaceBefore) env (Record.written value) (Record.synced value) 7
      (by decide +kernel) (Record.written_valid value) (Record.written_ready value) (Record.sync_step value))
  simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  exact Publish.directory_prefix env (Record.synced value) 7 (by decide +kernel)

@[expose] def committed : Phase → Bool
  | .beforeDirectoryClose | .finished => true
  | _ => false
@[expose] def phaseWater : Phase → Nat
  | .beforeFileSync | .beforeDirectoryOpen => 8
  | _ => 9
@[expose] def durable (value : U16) : Phase → ByteArray
  | .beforeFileSync => ByteArray.empty
  | _ => Record.content value
@[expose] def namespaceScript : Phase → Term
  | .beforeFileSync | .beforeDirectoryOpen => Publish.opening
  | _ => .nil

private theorem namespace_view (env : Environment) (value : U16) (phase : Phase) :
    namespaceSnapshot (phaseEnv env value phase) =
      some {Publish.namespaceAfter (committed phase) with script := namespaceScript phase} := by
  cases phase <;>
    simp [phaseEnv,committed,namespaceScript,decodedEnv,Publish.directoryEnv,frame,
      Publish.namespaceBefore,Publish.namespaceAfter,namespaceSnapshot,namespaceTable,
      namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,List.eraseDups_cons,
      tablesEqual,Publish.names,Publish.valid_path]

private theorem inode_view (env : Environment) (value : U16) (phase : Phase) :
    inode 1 (phaseEnv env value phase) =
      some ⟨Record.content value,durable value phase,0,.nil⟩ := by
  cases phase <;>
    simp [phaseEnv,durable,decodedEnv,Publish.directoryEnv,frame,Record.written,Record.synced,
      inode,decode,encode,limit,Record.content_size,List.filter,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

private theorem inode_cells (env : Environment) (value : U16) (phase : Phase) :
    (phaseEnv env value phase).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Record.content value,durable value phase,0,.nil⟩)] := by
  cases phase <;>
    simp [phaseEnv,durable,decodedEnv,Publish.directoryEnv,frame,Record.written,Record.synced,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

/-- All admitted names, inode images and watermarks are retained. Data fsync
fixes file bytes; only directory fsync rules out losing the name. -/
theorem phase_crash (env : Environment) (value : U16) (phase : Phase) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (phaseEnv env value phase) = some image) :
    ∃ mask contents, masks = [(1,mask)] ∧
      persist (durable value phase) (Record.content value) mask = some contents ∧
      image.inodes = [(1,contents)] ∧ image.highWater = phaseWater phase ∧
      (image.names = [] ∨ image.names = Publish.names) ∧
      (committed phase = true → image.names = Publish.names) := by
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names,published⟩ :=
    Publish.crash_shape (phaseEnv env value phase)
      ⟨Record.content value,durable value phase,0,.nil⟩ (committed phase) (namespaceScript phase)
      (namespace_view env value phase) (inode_cells env value phase) (inode_view env value phase)
      chosen masks image accepted
  refine ⟨mask,contents,masksEq,saved,inodes,?_,names,published⟩
  cases phase <;> exact water

private theorem fixed_after_sync (value : U16) (phase : Phase) (synced : phase ≠ .beforeFileSync)
    (mask contents : ByteArray)
    (saved : persist (durable value phase) (Record.content value) mask = some contents) :
    contents = Record.content value := by
  cases phase
  · contradiction
  all_goals exact Publish.persist_equal_images _ _ _ saved

/-- Every admitted phase image has a verified consistent ready recovery. Before
data fsync it may reject a torn record; a lost name propagates opening failure. -/
theorem phase_recovery (env : Environment) (value : U16) (phase : Phase) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks (phaseEnv env value phase) = some image) :
    (∃ residual, Result.ReadyPrefix (file_resource_commit ⟨3,8⟩)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase)) ∧
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  refine ⟨phase_prefix env value phase,?_⟩
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names,published⟩ :=
    phase_crash env value phase chosen masks image accepted
  have valid : 1 ≤ phaseWater phase := by cases phase <;> decide +kernel
  have bound : contents.size ≤ 4 := by
    by_cases synced : phase = .beforeFileSync
    · exact ShortRecovery.fresh_image_size value mask contents (by simpa [synced,durable] using saved)
    · rw [fixed_after_sync value phase synced mask contents saved,Record.content_size]
  rcases names with absent | retained
  · have imageEq : image = ⟨[],[(1,contents)],phaseWater phase⟩ := by cases image; simp_all
    refine ⟨ShortRecovery.missingChoice error,
      ShortRecovery.missingBoot contents (phaseWater phase) error,
      ShortRecovery.missingDone contents (phaseWater phase),.Err ⟨error⟩,?_,
      ShortRecovery.missing_recovery contents (phaseWater phase) error,Or.inl rfl⟩
    rw [imageEq]
    exact ShortRecovery.missing_restart contents (by simp only [limit]; omega) _ valid error
  · have imageEq : image = ⟨Publish.names,[(1,contents)],phaseWater phase⟩ := by cases image; simp_all
    by_cases synced : phase = .beforeFileSync
    · obtain ⟨script,before,after,result,restarted,recovered,allowed⟩ :=
        ShortRecovery.persisted_image_recovery value mask contents
          (by simpa [synced,durable] using saved) (phaseWater phase) valid
      refine ⟨script,before,after,.Ok result,?_,recovered,Or.inr ?_⟩
      · rw [imageEq]; exact restarted
      · rcases allowed with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
    · have same := fixed_after_sync value phase synced mask contents saved
      subst contents
      refine ⟨RecordRecovery.openingScript,
        RecordRecovery.boot (Record.low value) (Record.high value)
          (Record.low (~~~value)) (Record.high (~~~value)) (phaseWater phase),
        RecordRecovery.scan (Record.low value) (Record.high value)
          (Record.low (~~~value)) (Record.high (~~~value)) (phaseWater phase) 4 .nil true,
        .Ok (some value),?_,RecordRecovery.recover_value value _ valid,Or.inr (Or.inr rfl)⟩
      rw [imageEq,RecordRecovery.content_layout]
      exact RecordRecovery.restart_image _ _ _ _ _ valid

/-- Once data fsync has completed, every admitted retained-name image recovers
exactly the original value; directory fsync additionally guarantees retention. -/
theorem post_sync_recovery (env : Environment) (value : U16) (phase : Phase)
    (synced : phase ≠ .beforeFileSync) (chosen : Names) (masks : List (Nat × ByteArray))
    (image : FilesystemImage) (retained : image.names = Publish.names)
    (accepted : filesystemCrashImage chosen masks (phaseEnv env value phase) = some image) :
    restartFilesystem image RecordRecovery.openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) =
      (.ok (.Ok (some value)),RecordRecovery.scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater 4 .nil true) := by
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names,published⟩ :=
    phase_crash env value phase chosen masks image accepted
  have same := fixed_after_sync value phase synced mask contents saved
  subst contents
  have imageEq : image = ⟨Publish.names,[(1,Record.content value)],phaseWater phase⟩ := by cases image; simp_all
  have valid : 1 ≤ phaseWater phase := by cases phase <;> decide +kernel
  rw [imageEq]
  refine ⟨?_,RecordRecovery.recover_value value _ valid⟩
  rw [RecordRecovery.content_layout]
  exact RecordRecovery.restart_image _ _ _ _ _ valid

/-- After both synchronizations, all admitted crashes preserve the name and
value, including crashes before directory destruction or the NIF return. -/
theorem directory_sync_recovery (env : Environment) (value : U16) (phase : Phase)
    (published : committed phase = true) (chosen : Names) (masks : List (Nat × ByteArray))
    (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (phaseEnv env value phase) = some image) :
    (∃ residual, Result.ReadyPrefix (file_resource_commit ⟨3,8⟩)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase)) ∧
    restartFilesystem image RecordRecovery.openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) =
      (.ok (.Ok (some value)),RecordRecovery.scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater 4 .nil true) := by
  obtain ⟨mask,contents,masksEq,saved,inodes,water,names,forced⟩ :=
    phase_crash env value phase chosen masks image accepted
  have synced : phase ≠ .beforeFileSync := by intro same; simp [same,committed] at published
  exact ⟨phase_prefix env value phase,
    post_sync_recovery env value phase synced chosen masks image (forced published) accepted⟩

private theorem full_bytes (value : U16) (phase : Phase) :
    persist (durable value phase) (Record.content value) (RecordRecovery.tearingMask true true true true) =
      some (Record.content value) := by
  cases phase <;> simp only [durable]
  · simpa [RecordRecovery.tornData,Record.selected,RecordRecovery.content_layout] using
      RecordRecovery.persist_torn value true true true true
  all_goals rw [RecordRecovery.content_layout]
  all_goals rfl

private theorem water_view (env : Environment) (value : U16) (phase : Phase) :
    (phaseEnv env value phase).nativeRefCounter = phaseWater phase := by
  cases phase <;> rfl

/-- Every phase is executable and admits a full-content persistent image. -/
theorem phase_witness (env : Environment) (value : U16) (phase : Phase) :
    (∃ residual, Result.ReadyPrefix (file_resource_commit ⟨3,8⟩)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase)) ∧
    filesystemCrashImage Publish.names [(1,RecordRecovery.tearingMask true true true true)]
      (phaseEnv env value phase) =
      some ⟨Publish.names,[(1,Record.content value)],phaseWater phase⟩ := by
  refine ⟨phase_prefix env value phase,?_⟩
  simp only [filesystemCrashImage,namespace_view,inode_cells,Bind.bind,Option.bind_some]
  cases phase <;>
    simp [committed,namespaceScript,Publish.namespaceAfter,Publish.names,namespaceTable,namespaceEntry,
      encodeNames,List.eraseDups_cons,namespaceCrashAllowed,namedInode,Publish.valid_path,
      inode_view,full_bytes,Bind.bind,water_view,phaseWater]

/-- Data fsync alone does not guarantee namespace retention. The lost-name
image is concrete at every reachable phase before directory fsync. -/
theorem lost_name_witness (env : Environment) (value : U16) (phase : Phase)
    (pending : committed phase = false) :
    (∃ residual, Result.ReadyPrefix (file_resource_commit ⟨3,8⟩)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase)) ∧
    filesystemCrashImage [] [(1,RecordRecovery.tearingMask true true true true)]
      (phaseEnv env value phase) = some ⟨[],[(1,Record.content value)],phaseWater phase⟩ := by
  refine ⟨phase_prefix env value phase,?_⟩
  simp only [filesystemCrashImage,namespace_view,inode_cells,Bind.bind,Option.bind_some]
  cases phase <;> simp only [committed,Bool.true_eq_false] at pending
  all_goals simp [committed,namespaceScript,Publish.namespaceAfter,Publish.names,namespaceTable,
    encodeNames,namespaceCrashAllowed,namedInode,
    inode_view,full_bytes,Bind.bind,water_view,phaseWater]

/-- The actual compiled Rustler facade and Lynx panic/encoding adapter retain
every native I/O phase, with release and result encoding left in the residual. -/
theorem nif_phase_prefix (env : Environment) (value : U16) (phase : Phase) :
    ∃ residual, Result.ReadyPrefix (Rustler.executeNative (__COMMIT__ ⟨3,8⟩) Rustler.encodeBool)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase) := by
  obtain ⟨remaining,trace⟩ := phase_prefix env value phase
  let finish (outcome : core.result.Result Unit NativeIoError) : NativeM Bool := do
    file_resource_release ⟨3,8⟩
    match outcome with
    | .Ok _ => NativeM.ok true
    | .Err error => do
      NativeOwnedDrop.drop error
      NativeM.ok false
  have compiled : __COMMIT__ ⟨3,8⟩ = file_resource_commit ⟨3,8⟩ >>= finish := rfl
  refine ⟨Rustler.executeNative (remaining >>= finish) Rustler.encodeBool,?_⟩
  rw [compiled]
  exact Rustler.executeNative_readyPrefix (trace.bind finish) Rustler.encodeBool

/-- The compiled facade reaches the selected phase, and every admitted crash
image has the verified consistent Rust recovery execution. -/
theorem nif_phase_recovery (env : Environment) (value : U16) (phase : Phase) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks (phaseEnv env value phase) = some image) :
    (∃ residual, Result.ReadyPrefix (Rustler.executeNative (__COMMIT__ ⟨3,8⟩) Rustler.encodeBool)
      (phaseEnv env value .beforeFileSync) residual (phaseEnv env value phase)) ∧
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  exact ⟨nif_phase_prefix env value phase,(phase_recovery env value phase chosen masks image error accepted).2⟩

end FileResource.CommitPhases
