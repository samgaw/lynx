module
public import FileResource.CallPrefix
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.CommitFailure
open NativeFile FileResource.CreatedCalls FileResource.Creation

/-- The host admits one callback-free OS error capability for the selected
failure. This is not a proof of native error allocation or reclamation. -/
@[expose] def errorCell : Nat × String × Term := (10,NativeIoError.typeName,.atom "live")
@[expose] def errorScript (mask : ByteArray) (rest : Term := .nil) : Term :=
  .cons (.tuple #[.atom "sync_all",.atom "error",.integer 10,.bitstring mask 0]) rest
@[expose] def before (value : U16) (mask : ByteArray) (rest : Term := .nil) : State :=
  ⟨Record.content value,ByteArray.empty,4,errorScript mask rest⟩
@[expose] def after (value : U16) (saved : ByteArray) (rest : Term := .nil) : State :=
  ⟨Record.content value,saved,4,rest⟩

@[expose] def initial (env : Environment) (state : State) : Environment :=
  {env with refCounter := 10,nativeHeap := errorCell ::
    NativeResourceArc.vmCells payload 3 5 6 ++ frame state Publish.namespaceBefore}
@[expose] def decoded (env : Environment) (state : State) : Environment :=
  {env with refCounter := 11,nativeHeap := [
    (11,NativeResourceArc.handleType effects_native.FileResource,.reference 3),errorCell,
    (6,NativeResourceArc.termType effects_native.FileResource,.tuple #[.reference 3,.reference 5]),
    (5,NativeResourceArc.handleType effects_native.FileResource,.reference 3),
    (3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])]
      ++ frame state Publish.namespaceBefore}
@[expose] def released (env : Environment) (state : State) : Environment :=
  {env with refCounter := 11,nativeHeap := errorCell ::
    NativeResourceArc.vmCells payload 3 5 6 ++ frame state Publish.namespaceBefore}
@[expose] def done (env : Environment) (state : State) : Environment :=
  {env with refCounter := 11,nativeHeap :=
    NativeResourceArc.vmCells payload 3 5 6 ++ frame state Publish.namespaceBefore}

private theorem pinned (env : Environment) (state : State) :
    NativeResourceArc.Pinned payload 3 5 6 (initial env state) := by
  constructor
  · simp [initial]
  · intro cell member
    simp only [initial,errorCell,NativeResourceArc.vmCells,frame,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [initial]
  · simp [initial,errorCell,NativeResourceArc.vmCells,frame]
  · simp [initial,errorCell,NativeResourceArc.vmCells,frame]
  · simp [initial,errorCell,NativeResourceArc.vmCells,frame]
  · simp [initial,errorCell,NativeResourceArc.vmCells,frame,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      NativeIoError.typeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem decode_prefix (env : Environment) (state : State)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.reference 6)) (initial env state)
      (.ok (⟨3,11⟩ : NativeResourceArc effects_native.FileResource)) (decoded env state) := by
  simpa [initial,decoded,NativeResourceArc.vmCells,frame,errorCell,List.map] using
    NativeResourceArc.decode_pinned_prefix payload (initial env state) 3 5 6 (pinned env state) registered

private theorem views (env : Environment) (state : State) :
    (decoded env state).nativeHeap.filter (fun cell => cell.1 == 11) =
      [(11,NativeResourceArc.handleType effects_native.FileResource,.reference 3)] ∧
    (decoded env state).nativeHeap.filter (fun cell => cell.1 == 3) =
      [(3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])] ∧
    ((decoded env state).nativeHeap.filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType effects_native.FileResource && cell.2.2 == .reference 3)).length = 2 := by
  simp [decoded,errorCell,frame,List.filter,NativeIoError.typeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName]

private theorem borrowed (env : Environment) (state : State) :
    Result.ReadyPrefix (NativeResourceArc.deref (⟨3,11⟩ : NativeResourceArc effects_native.FileResource))
      (decoded env state) (.ok payload) (decoded env state) := by
  obtain ⟨token,stored,owners⟩ := views env state
  exact NativeResourceArc.deref_retained_prefix _ _ _ token stored owners

theorem sync_poll (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term := .nil) :
    pollSync ⟨2⟩ (decoded env (before value mask rest)) =
      some (.ok (.Err ⟨10⟩),decoded env (after value saved rest)) := by
  simp [pollSync,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,decoded,frame,errorCell,
    before,after,errorScript,inode,decode,encode,limit,Record.content_size,blocked,syncStep,action,persisted,
    store,sharedStore,List.filter,List.map,NativeIoError.typeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName,typeName,handleTypeName]

/-- The actual Rust question-mark branch returns the selected fsync error with
the persisted image retained, and never opens or synchronizes the directory. -/
theorem commit_prefix (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term := .nil) :
    Result.ReadyPrefix (file_resource_commit ⟨3,11⟩) (decoded env (before value mask rest))
      (.ok (.Err ⟨10⟩)) (decoded env (after value saved rest)) := by
  simp only [file_resource_commit,file_resource_sync,monadLift_self,bind_assoc]
  apply ((borrowed env (before value mask rest)).bind _).trans
  simp only [Result.ok_bind,payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (sync_poll env value mask saved persisted rest)
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.monadLift_eq,NativeM.fromRust]
  exact .refl _ _

/-- Nonfinal resource release retains both the VM pin and the admitted error,
with every mutation made by the failing operation preserved. -/
theorem release_prefix (env : Environment) (state : State) :
    Result.ReadyPrefix (file_resource_release ⟨3,11⟩) (decoded env state) (.ok ()) (released env state) := by
  obtain ⟨token,stored,owners⟩ := views env state
  simp only [file_resource_release,monadLift_self,NativeOwnedDrop.drop]
  have trace := NativeResourceArc.releaseOwned_retained_prefix
    (⟨3,11⟩ : NativeResourceArc effects_native.FileResource) payload _ token stored owners
  convert trace using 1
  simp [decoded,released,errorCell,frame,NativeResourceArc.vmCells,List.filter,List.map]

/-- The actual standard error destructor consumes exactly its unique admitted
capability. No error allocation or custom-payload cleanup is inferred here. -/
theorem error_prefix (env : Environment) (state : State) :
    Result.ReadyPrefix (NativeOwnedDrop.drop (⟨10⟩ : NativeIoError)) (released env state)
      (.ok ()) (done env state) := by
  simp only [NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability]
  apply Result.ReadyPrefix.get
  simp [released,done,errorCell,frame,NativeResourceArc.vmCells,List.filter,NativeIoError.typeName]
  apply Result.ReadyPrefix.set
  exact .refl _ _

/-- Actual compiled Rustler failure handling releases its resource owner,
destroys the admitted OS error and returns false without rolling back disk state. -/
theorem facade_prefix (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term := .nil) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,11⟩) (decoded env (before value mask rest))
      (.ok false) (done env (after value saved rest)) := by
  simp only [__COMMIT__,monadLift_self]
  apply ((commit_prefix env value mask saved persisted rest).bind _).trans
  simp only [Result.ok_bind]
  apply ((release_prefix env (after value saved rest)).bind _).trans
  simp only [Result.ok_bind]
  apply ((error_prefix env (after value saved rest)).bind _).trans
  simp only [Result.ok_bind,NativeM.ok]
  exact .refl _ _

@[expose] def invoke : Result := do
  let owner ← NativeResourceArc.decode (.reference 6)
  Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool

/-- The modeled remote invocation returns Elixir false while the VM resource
remains live and the failed synchronization's allowed persistent image survives. -/
theorem invocation_prefix (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (rest : Term := .nil) :
    Result.ReadyPrefix invoke (initial env (before value mask rest)) (.ok Term.false)
      (done env (after value saved rest)) := by
  simp only [invoke]
  apply ((decode_prefix env (before value mask rest) registered).bind _).trans
  simp only [Result.ok_bind]
  simpa [Rustler.executeNative,Result.ok_bind,Result.handle,Rustler.encodeBool] using
    Rustler.executeNative_readyPrefix (facade_prefix env value mask saved persisted rest) Rustler.encodeBool

/-- The exact invocation equation is usable by ordinary translated Elixir callers. -/
theorem call_run (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (rest : Term := .nil) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) (initial env (before value mask rest)) =
      (.ok Term.false,done env (after value saved rest)) := by
  simpa only [invoke,Result.ok_apply] using (invocation_prefix env value mask saved persisted registered rest).apply

/-- A failure continuation observes false and the actual retained persistent
state, rather than an acquisition snapshot or a silently consumed VM pin. -/
theorem failure_env {α : Type} (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved)
    (rest : Term) (next : Term → Result α) (env : Environment) (counter : env.refCounter = 10)
    (heap : env.nativeHeap = errorCell :: NativeResourceArc.vmCells payload 3 5 6 ++
      frame (before value mask rest) Publish.namespaceBefore)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      let result ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      next result) env = next Term.false (done env (after value saved rest)) := by
  have trace := ((invocation_prefix env value mask saved persisted registered rest).bind next).apply
  simpa only [invoke,Result.ok_bind,initial,← heap,← counter,bind_assoc] using trace

theorem after_valid (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved) (rest : Term) :
    Valid (after value saved rest) := by
  have bound := ShortRecovery.fresh_image_size value mask saved persisted
  simp [Valid,after,Record.content_size,limit]
  omega

theorem retry_step (value : U16) (saved : ByteArray) :
    syncStep (after value saved (syncChoice .nil)) = some (.Ok (),Record.synced value) := by
  simp [syncStep,after,syncChoice,action,Record.synced]

/-- The same actual resource remains usable: a successful second call commits
its original visible bytes after the first call failed and destroyed its error. -/
theorem retry_run (env : Environment) (value : U16) (mask saved : ByteArray)
    (persisted : persist ByteArray.empty (Record.content value) mask = some saved)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      let first ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      let owner ← NativeResourceArc.decode (.reference 6)
      let second ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      Result.ok (first,second)) (initial env (before value mask (syncChoice .nil))) =
      (.ok (Term.false,Term.true),Publish.committedEnv env (Record.synced value) 11) := by
  rw [failure_env value mask saved persisted (syncChoice .nil) _
    (initial env (before value mask (syncChoice .nil))) rfl rfl (by simpa [initial] using registered)]
  have continued := Publish.commit_env_state
    (after value saved (syncChoice .nil)) (Record.synced value)
    (after_valid value mask saved persisted _) (by rfl) (retry_step value saved)
    (fun second => Result.ok (Term.false,second)) (done env (after value saved (syncChoice .nil)))
    (by simp [done]) rfl (by simpa [done] using registered)
  simpa [Result.ok_bind,Result.ok_apply,initial,done,Publish.committedEnv] using continued

/-- A failed fsync may already have written four bytes; failure is not rollback. -/
theorem zero_saved (value : U16) :
    persist ByteArray.empty (Record.content value) ⟨#[0,0,0,0]⟩ = some ⟨#[0,0,0,0]⟩ := by
  simpa [RecordRecovery.tearingMask,RecordRecovery.tornData,RecordRecovery.data,Record.selected] using
    RecordRecovery.persist_torn value false false false false

@[expose] def seed : Environment :=
  initial (({} : Environment).setPdict [(.atom "resource",.reference 6)])
    (before 4660#u16 ⟨#[0,0,0,0]⟩ (syncChoice .nil))

end FileResource.CommitFailure
