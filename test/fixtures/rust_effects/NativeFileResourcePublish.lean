module
public import FileResource.Write
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Publish
open NativeFile FileResource.Creation FileResource.CreatedCalls

@[expose] def names : Names := [(path,1)]
@[expose] def actionOk (operation : String) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer 0,.bitstring ByteArray.empty 0]) rest
@[expose] def closeScript : Term := actionOk "close_dir" .nil
@[expose] def syncScript : Term := actionOk "sync_dir" closeScript
@[expose] def opening : Term :=
  .cons (.tuple #[.atom "open",.bitstring ⟨#[46]⟩ 0,.atom "ok",.integer 0,syncScript]) .nil
@[expose] def namespaceBefore : NamespaceSnapshot := ⟨names,[],[names],opening⟩
@[expose] def namespaceAfter (committed : Bool) : NamespaceSnapshot :=
  ⟨names,(if committed then names else []),(if committed then [] else [names]),.nil⟩

@[expose] def directoryEnv (env : Environment) (state : State) (counter : Nat)
    (committed closed : Bool) (script : Term) : Environment :=
  {decodedEnv env state counter (namespaceAfter committed) with
    nativeRefCounter := counter + 2
    nativeHeap := (counter + 2,(if closed then closedDirectoryTypeName else directoryTypeName),.tuple #[script]) ::
      (decodedEnv env state counter (namespaceAfter committed)).nativeHeap}

theorem dot_bytes : bytes (toStr ".") = (⟨#[46]⟩ : ByteArray) := by
  simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse]
  exact ⟨46,by decide +kernel,by decide +kernel⟩

theorem valid_path : supportedPath path = true := by
  unfold path supportedPath
  decide +kernel

set_option maxHeartbeats 1000000 in
theorem open_poll (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    pollOpenReadOnly (toStr ".") (decodedEnv env state counter namespaceBefore) =
      some (.ok (.Ok ⟨counter + 2⟩),directoryEnv env state counter false false syncScript) := by
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have b3 : (counter == 3) = false := by simp; omega
  have b4 : (counter == 4) = false := by simp; omega
  have p0 : counter ≠ 0 := by omega
  have p1 : counter ≠ 1 := by omega
  have p3 : counter ≠ 3 := by omega
  have p4 : counter ≠ 4 := by omega
  simp [p0,List.eraseDups_cons,pollOpenReadOnly,dot_bytes,supportedOpenPath,decodedEnv,directoryEnv,frame,
    namespaceBefore,namespaceAfter,names,namespaceState,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,
    valid_path,openChoice,pathChoice,opening,replaceNamespaceScript,
    b0,b1,b3,b4]

set_option maxHeartbeats 1000000 in
theorem sync_poll (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    pollSync ⟨counter + 2⟩ (directoryEnv env state counter false false syncScript) =
      some (.ok (.Ok ()),directoryEnv env state counter true false closeScript) := by
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have b3 : (counter == 3) = false := by simp; omega
  have b4 : (counter == 4) = false := by simp; omega
  have p0 : counter ≠ 0 := by omega
  have p1 : counter ≠ 1 := by omega
  have p3 : counter ≠ 3 := by omega
  have p4 : counter ≠ 4 := by omega
  simp [p0,p1,p3,p4,List.eraseDups_cons,pollSync,lookup,pollDirectorySync,directoryHandle,directoryEnv,decodedEnv,frame,
    namespaceAfter,names,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,valid_path,syncScript,closeScript,actionOk,action,
    storeDirectory,storeNamespace,b0,b1,b3,b4,typeName,handleTypeName,writableHandleTypeName,
    directoryTypeName]

set_option maxHeartbeats 1000000 in
theorem close_poll (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    pollClose ⟨counter + 2⟩ (directoryEnv env state counter true false closeScript) =
      some (.ok (),directoryEnv env state counter true true .nil) := by
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have b3 : (counter == 3) = false := by simp; omega
  have b4 : (counter == 4) = false := by simp; omega
  have p0 : counter ≠ 0 := by omega
  have p1 : counter ≠ 1 := by omega
  have p3 : counter ≠ 3 := by omega
  have p4 : counter ≠ 4 := by omega
  simp [p0,p1,p3,p4,pollClose,lookup,pollDirectoryClose,directoryHandle,directoryEnv,decodedEnv,frame,
    namespaceAfter,closeScript,actionOk,action,storeDirectory,
    b0,b1,b3,b4,typeName,handleTypeName,writableHandleTypeName,directoryTypeName]

/-- Actual opening, directory fsync and compiler-generated destruction preserve the live resource owner. -/
theorem directory_prefix (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    Result.ReadyPrefix effects_core.synchronize_directory
      (decodedEnv env state counter namespaceBefore) (.ok (.Ok ()))
      (directoryEnv env state counter true true .nil) := by
  simp only [effects_core.synchronize_directory,monadLift_self,openReadOnly,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok (.Ok ⟨counter + 2⟩)) _ _ _ _ (open_poll env state counter bounded)
  simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch,syncAll,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok (.Ok ())) _ _ _ _ (sync_poll env state counter bounded)
  simp only [Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok ()) _ _ _ _ (close_poll env state counter bounded)
  simpa [NativeM.ok] using Result.ReadyPrefix.refl
    (Result.ok (.Ok () : core.result.Result Unit NativeIoError)) (directoryEnv env state counter true true .nil)

@[expose] def committedEnv (env : Environment) (state : State) (counter : Nat) : Environment :=
  {env with nativeRefCounter := counter + 2, nativeHeap :=
    (counter + 2,closedDirectoryTypeName,.tuple #[.nil]) ::
      NativeResourceArc.vmCells payload 3 5 6 ++ frame state (namespaceAfter true)}

private theorem directory_owner (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    (directoryEnv env state counter true true .nil).nativeHeap.filter (fun cell => cell.1 == counter + 1) =
      [(counter + 1,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 3)] ∧
    (directoryEnv env state counter true true .nil).nativeHeap.filter (fun cell => cell.1 == 3) =
      [(3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])] ∧
    ((directoryEnv env state counter true true .nil).nativeHeap.filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType effects_native.FileResource && cell.2.2 == .nativeReference 3)).length = 2 := by
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have b2 : (counter == 2) = false := by simp; omega
  have b4 : (counter == 4) = false := by simp; omega
  have b5 : (counter == 5) = false := by simp; omega
  have p1 : counter ≠ 1 := by omega
  simp [directoryEnv,decodedEnv,frame,List.filter,b0,b1,b2,b4,b5,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName,closedDirectoryTypeName]

private theorem release_after_directory {α β : Type} (env : Environment) (state : State)
    (counter : Nat) (bounded : 6 ≤ counter) (finish : Result α) (handler : Exception → Result α)
    (next : α → Result β) :
    ((Result.handle (do
      NativeResourceArc.releaseOwned (⟨3,counter + 1⟩ : NativeResourceArc effects_native.FileResource)
      finish) handler) >>= next) (directoryEnv env state counter true true .nil) =
    ((Result.handle finish handler) >>= next) (committedEnv env state counter) := by
  obtain ⟨token,stored,owners⟩ := directory_owner env state counter bounded
  rw [NativeResourceArc.releaseOwned_retained_handled_next _ payload _ _ _ _ token stored owners]
  have n0 : (counter != 0) = true := by simp; omega
  have n1 : (counter != 1) = true := by simp; omega
  have n2 : (counter != 2) = true := by simp; omega
  have n4 : (counter != 4) = true := by simp; omega
  have n5 : (counter != 5) = true := by simp; omega
  have p1 : counter ≠ 1 := by omega
  congr 1
  simp [directoryEnv,decodedEnv,committedEnv,NativeResourceArc.vmCells,frame,
    List.filter,List.map,n0,n1,n2,n4,n5,p1]

/-- The actual facade synchronizes data and namespace while retaining the same file resource. -/
theorem commit_next_state {α : Type} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (),after)) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      next result) (pinnedEnv env before counter namespaceBefore) =
      next Term.true (committedEnv env after counter) := by
  simp only [__COMMIT__,file_resource_commit,file_resource_sync,monadLift_self,
    Rustler.executeNative,bind_assoc]
  rw [borrowed_next (ns := namespaceBefore) env before counter bounded _ _ _ registered]
  simp only [payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind,Result.handle]
  rw [Result.wait_ready_apply _ _ _ _ _ (file_sync_poll (ns := namespaceBefore) env
    before after counter bounded valid
    ready step)]
  simp only [Result.ok_bind,NativeM.monadLift_eq,NativeM.fromRust_ok,
    core.result.Result.Insts.CoreOpsTry.branch]
  have trace := directory_prefix env after counter bounded
  rw [(((trace.bind _).handle _).bind _).apply]
  simp only [Result.ok_bind,file_resource_release,monadLift_self,NativeOwnedDrop.drop,NativeM.ok]
  have released := release_after_directory env after counter bounded
    (Result.ok Term.true) (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted) next
  convert released using 1 <;> try simp [Result.handle,Rustler.encodeBool]
  all_goals congr 1

theorem commit_next {α : Type} (env : Environment) (value : U16) (counter : Nat)
    (bounded : 6 ≤ counter) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      next result) (pinnedEnv env (Write.written value) counter namespaceBefore) =
      next Term.true (committedEnv env (Write.synced value) counter) := by
  exact commit_next_state env _ _ counter bounded (Write.written_valid value)
    (Write.written_ready value) (Write.sync_step value) next registered

/-- Use the commitment contract in the caller's current runtime environment. -/
theorem commit_env_state {α : Type} (before after : State)
    (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (),after)) (next : Term → Result α) (env : Environment)
    (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame before namespaceBefore)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      next result) env = next Term.true (committedEnv env after env.nativeRefCounter) := by
  simpa only [pinnedEnv,← heap] using commit_next_state env before after env.nativeRefCounter bounded valid ready step next registered

theorem commit_env {α : Type} (value : U16) (next : Term → Result α) (env : Environment)
    (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame (Write.written value) namespaceBefore)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool
      next result) env = next Term.true (committedEnv env (Write.synced value) env.nativeRefCounter) := by
  simpa only [pinnedEnv,← heap] using commit_next env value env.nativeRefCounter bounded next registered

theorem commit_run_state (before after : State) (valid : Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (),after))
    (env : Environment) (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame before namespaceBefore)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) env =
      (.ok Term.true,committedEnv env after env.nativeRefCounter) := by
  simpa only [Result.bind_ok,Result.ok_apply] using
    commit_env_state before after valid ready step Result.ok env bounded heap registered

theorem commit_run (value : U16) (env : Environment) (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame (Write.written value) namespaceBefore)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) env =
      (.ok Term.true,committedEnv env (Write.synced value) env.nativeRefCounter) := by
  simpa only [Result.bind_ok,Result.ok_apply] using commit_env value Result.ok env bounded heap registered

@[expose] def seed : Environment := initial {} Write.before.script opening
@[expose] def done (env : Environment) (value : U16) : Environment := committedEnv env (Write.synced value) 7

theorem returned_before (env : Environment) :
    returned env Write.before.script opening = pinnedEnv env Write.before 6 namespaceBefore := rfl

/-- Actual creation and payload writing precede the file and directory commitment. -/
theorem create_write_commit (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) (initial env Write.before.script opening) =
      (.ok Term.true,done env value) := by
  rw [create_next (rest := opening) env Write.before.script _ registered,returned_before]
  rw [Write.write_next (ns := namespaceBefore) env Write.before (Write.written value) 6 (by omega)
    Write.before_valid Write.before_ready value 2#usize (Write.full_step value) _ registered]
  simpa [Result.bind_ok,Result.ok_apply,Rustler.encodeBool,done] using
    commit_next env value 7 (by omega) Result.ok registered

theorem namespace_done (env : Environment) (value : U16) :
    namespaceSnapshot (done env value) = some (namespaceAfter true) := by
  simp [namespaceSnapshot,done,committedEnv,NativeResourceArc.vmCells,frame,
    namespaceAfter,names,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,valid_path]

theorem inode_done (env : Environment) (value : U16) :
    inode 1 (done env value) = some ⟨Write.content value,Write.content value,0,.nil⟩ := by
  simp [inode,done,committedEnv,NativeResourceArc.vmCells,frame,Write.synced,
    inodeTypeName,closedDirectoryTypeName,namespaceTypeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,decode,encode,Write.content_size,limit]

/-- Equal synchronized images are invariant under every admitted tearing mask. -/
theorem persist_equal_images (bytes mask result : ByteArray)
    (accepted : persist bytes bytes mask = some result) : result = bytes := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    have size : mask.size = bytes.size := by omega
    cases accepted
    apply ByteArray.ext
    apply _root_.Array.ext
    · simp [size]
    · intro index validMask validBytes
      have bounded : index < bytes.size := by simpa only [ByteArray.size_data] using validBytes
      simp [getElem!_pos,bounded]
      rfl
  · contradiction

private theorem inode_cells (env : Environment) (value : U16) :
    (done env value).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Write.content value,Write.content value,0,.nil⟩)] := by
  simp [done,committedEnv,NativeResourceArc.vmCells,frame,Write.synced,inodeTypeName,
    closedDirectoryTypeName,namespaceTypeName,writableHandleTypeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName]

theorem crash_contents (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (done env value) = some image) :
    image.inodes = [(1,Write.content value)] := by
  simp only [filesystemCrashImage,namespace_done,Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at accepted
  rcases accepted with ⟨selected,table,accepted⟩
  split at accepted
  · contradiction
  · rename_i allowed
    simp only [inode_cells,List.length_singleton,Nat.reduceGT] at accepted
    split at accepted
    · contradiction
    · rename_i keys
      have key_eq : masks.map (·.1) = [1] := by simpa using keys
      have shape : ∃ mask, masks = [(1,mask)] := by
        cases masks with
        | nil => simp at key_eq
        | cons head tail =>
          cases head with
          | mk id mask =>
            simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at key_eq
            obtain ⟨rfl,rfl⟩ := key_eq
            exact ⟨mask,rfl⟩
      obtain ⟨mask,rfl⟩ := shape
      simp only [List.mapM_cons,List.mapM_nil,Option.bind_eq_some_iff,inode_done,Option.bind_some,
        List.filter_cons,List.filter_nil,Nat.reduceBEq,↓reduceIte] at accepted
      rcases accepted with ⟨images,mapped,accepted⟩
      cases saved : persist (Write.content value) (Write.content value) mask with
      | none => simp [saved,Bind.bind] at mapped
      | some bytes =>
        have same := persist_equal_images (Write.content value) mask bytes saved
        subst bytes
        have image_eq : images = [(1,Write.content value)] := by
          simpa [saved,Bind.bind,Pure.pure] using mapped.symm
        subst images
        split at accepted
        · contradiction
        · cases accepted
          rfl

/-- The synchronized directory entry cannot disappear or name another inode in an admitted crash. -/
theorem crash_name (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (done env value) = some image) :
    namedInode image.names path = some 1 := by
  simp only [filesystemCrashImage,namespace_done,Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at accepted
  rcases accepted with ⟨selected,table,accepted⟩
  split at accepted
  · contradiction
  · rename_i allowed
    have good : namedInode selected path = some 1 := by
      have admitted : namespaceCrashAllowed (namespaceAfter true) selected = true := by simpa using allowed
      simp [namespaceCrashAllowed,namespaceAfter,names,namedInode] at admitted
      obtain ⟨actual,found⟩ := admitted.2
      simp [namedInode,found]
    split at accepted
    · contradiction
    · simp only [Option.bind_eq_some_iff] at accepted
      rcases accepted with ⟨images,mapped,accepted⟩
      split at accepted
      · contradiction
      · cases accepted
        exact good

@[expose] def zeroMask (bytes : ByteArray) : ByteArray := ⟨_root_.Array.replicate bytes.size 0⟩

private theorem persist_zero (bytes : ByteArray) : persist bytes bytes (zeroMask bytes) = some bytes := by
  have conditions : bytes.size ≤ (zeroMask bytes).size ∧
      (zeroMask bytes).size ≤ bytes.size ∧
      ((zeroMask bytes).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [zeroMask, ← ByteArray.size_data]
  let result : ByteArray := ⟨(zeroMask bytes).data.mapIdx fun index choice =>
    if choice == 1 then bytes[index]! else bytes[index]!⟩
  have accepted : persist bytes bytes (zeroMask bytes) = some result := by
    unfold persist
    simp only [Nat.min_self, Nat.max_self]
    rw [ite_eq_left conditions]
  rw [persist_equal_images bytes (zeroMask bytes) result accepted] at accepted
  exact accepted

/-- A concrete admitted image ensures the universal crash guarantee is not vacuous. -/
theorem admitted_crash (env : Environment) (value : U16) :
    filesystemCrashImage names [(1,zeroMask (Write.content value))] (done env value) =
      some ⟨names,[(1,Write.content value)],9⟩ := by
  simp only [filesystemCrashImage,namespace_done,inode_cells,Bind.bind,Option.bind_some]
  simp [namespaceAfter,names,namespaceTable,namespaceEntry,encodeNames,
    List.eraseDups_cons,namespaceCrashAllowed,namedInode,valid_path,inode_done,
    persist_zero,Bind.bind]
  rfl

/-- Every admitted crash after the actual acknowledged protocol preserves its name and payload. -/
theorem acknowledged_crash (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) (initial env Write.before.script opening) =
      (.ok Term.true,done env value) ∧
    filesystemCrashImage names [(1,zeroMask (Write.content value))] (done env value) =
      some ⟨names,[(1,Write.content value)],9⟩ ∧
    (∀ chosen masks image, filesystemCrashImage chosen masks (done env value) = some image →
      namedInode image.names path = some 1 ∧ image.inodes = [(1,Write.content value)]) := by
  refine ⟨create_write_commit env value registered,admitted_crash env value,?_⟩
  intro chosen masks image accepted
  exact ⟨crash_name env value chosen masks image accepted,crash_contents env value chosen masks image accepted⟩

private theorem namespace_choices (published : Bool) (script : Term) (selected : Names)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed {Publish.namespaceAfter published with script := script} selected = true) :
    selected = [] ∨ selected = Publish.names := by
  cases published <;>
    simp [namespaceCrashAllowed,Publish.namespaceAfter,Publish.names,namedInode] at allowed
  all_goals
    have mapped : selected.map (fun entry => entry.1.data) =
        List.replicate selected.length Creation.path.data := by
      apply List.map_eq_replicate_iff.mpr
      intro entry member
      exact (allowed.1 entry.1 entry.2 member).symm
    rw [mapped] at unique
    cases selected with
    | nil => exact Or.inl rfl
    | cons head tail =>
      have empty : tail = [] := by
        have length : tail.length = 0 := by
          simpa [List.replicate_succ,List.eraseDups_cons] using unique.symm
        exact List.eq_nil_of_length_eq_zero length
      subst tail
      have same : head.1 = Creation.path := by
        apply ByteArray.ext
        exact (allowed.1 head.1 head.2 (by simp)).symm
      cases head with
      | mk path id =>
        simp only at same
        subst path
        right
        simp at allowed
        simpa [Publish.names] using allowed

private theorem table_unique (chosen selected : Names)
    (table : namespaceTable (encodeNames chosen) = some selected) :
    (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length := by
  simp only [encodeNames,namespaceTable] at table
  split at table
  · contradiction
  · simp only [Bind.bind,Option.bind_eq_some_iff] at table
    rcases table with ⟨mapped,parsed,table⟩
    split at table
    · contradiction
    · rename_i unique
      cases table
      simpa using unique

/-- Crash projection for a single first-party inode and its publication history.
The premises expose only the relevant filesystem observations, so resources,
closed descriptors and other volatile ownership cells do not need new proofs. -/
theorem crash_shape (env : Environment) (state : State) (published : Bool) (script : Term)
    (snapshot : namespaceSnapshot env = some {namespaceAfter published with script := script})
    (nodes : env.nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode state)])
    (stored : inode 1 env = some state)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks env = some image) :
    ∃ mask contents, masks = [(1,mask)] ∧
      persist state.durable state.visible mask = some contents ∧
      image.inodes = [(1,contents)] ∧ image.highWater = env.nativeRefCounter ∧
      (image.names = [] ∨ image.names = names) ∧
      (published = true → image.names = names) := by
  simp only [filesystemCrashImage,snapshot,Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at accepted
  rcases accepted with ⟨selected,table,accepted⟩
  split at accepted
  · contradiction
  · rename_i allowed
    have admitted : namespaceCrashAllowed
        {Publish.namespaceAfter published with script := script} selected = true := by
      simpa using allowed
    have names := namespace_choices published script selected
      (table_unique chosen selected table) admitted
    have committedName : published = true → selected = Publish.names := by
      intro yes
      rcases names with absent | retained
      · subst selected
        simp [yes,namespaceCrashAllowed,Publish.namespaceAfter,Publish.names,namedInode] at admitted
      · exact retained
    simp only [nodes,List.length_singleton,Nat.reduceGT] at accepted
    split at accepted
    · contradiction
    · rename_i keys
      have key_eq : masks.map (·.1) = [1] := by simpa using keys
      have shape : ∃ mask, masks = [(1,mask)] := by
        cases masks with
        | nil => simp at key_eq
        | cons head tail =>
          cases head with
          | mk id mask =>
            simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at key_eq
            obtain ⟨rfl,rfl⟩ := key_eq
            exact ⟨mask,rfl⟩
      obtain ⟨mask,rfl⟩ := shape
      simp only [List.mapM_cons,List.mapM_nil,Option.bind_eq_some_iff,stored,Option.bind_some,
        List.filter_cons,List.filter_nil,Nat.reduceBEq,↓reduceIte] at accepted
      rcases accepted with ⟨images,mapped,accepted⟩
      cases saved : persist state.durable state.visible mask with
      | none => simp [saved,Bind.bind] at mapped
      | some contents =>
        have image_eq : images = [(1,contents)] := by
          simpa [saved,Bind.bind,Pure.pure] using mapped.symm
        subst images
        split at accepted
        · contradiction
        · cases accepted
          refine ⟨mask,contents,rfl,saved,rfl,rfl,names,committedName⟩

end FileResource.Publish
