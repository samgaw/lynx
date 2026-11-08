module
public import FileResource.RecordRecovery
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.RecordRetry
open NativeFile FileResource.RecordRecovery

/-- All ready operation boundaries of the actual four-byte checked reader. -/
inductive Phase where
  | beforeOpen | beforeByte0 | beforeByte1 | beforeByte2 | beforeByte3 | beforeClose | finished

@[expose] def phaseEnv (a b c d : U8) (generation : Nat) : Phase → Environment
  | .beforeOpen => boot a b c d generation
  | .beforeByte0 => scan a b c d generation 0 (readScript 4)
  | .beforeByte1 => scan a b c d generation 1 (readScript 3)
  | .beforeByte2 => scan a b c d generation 2 (readScript 2)
  | .beforeByte3 => scan a b c d generation 3 (readScript 1)
  | .beforeClose => scan a b c d generation 4 closeScript
  | .finished => scan a b c d generation 4 .nil true

@[expose] def phaseWater (generation : Nat) : Phase → Nat
  | .beforeOpen => generation
  | _ => generation + 1

/-- Each selected environment is reached by actual extracted recovery, retaining
its actual residual computation, including the integrity check and destructor. -/
theorem phase_prefix (a b c d : U8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    ∃ residual, Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (boot a b c d generation) residual (phaseEnv a b c d generation phase) := by
  cases phase <;> simp only [phaseEnv]
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (open_poll a b c d generation validGeneration)
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,effects_core.read_file_record,effects_core.read_file_word,
    NativeM.lift,monadLift_self,Array.to_slice_mut,Array.to_slice,Array.make_val,
    bind_assoc,effects_core.read_file_once,NativeFile.read,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (read_poll a b c d generation validGeneration 0 (by decide +kernel))
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [NativeM.ok]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (read_poll a b c d generation validGeneration 1 (by decide +kernel))
  · exact ⟨_,.refl _ _⟩
  all_goals simp [Array.from_slice,Recovery.one,Array.index_usize,
    NativeM.fromRust,Result.ok_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (read_poll a b c d generation validGeneration 2 (by decide +kernel))
  · exact ⟨_,.refl _ _⟩
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (read_poll a b c d generation validGeneration 3 (by decide +kernel))
  · exact ⟨_,.refl _ _⟩
  all_goals simp [NativeM.ok,Recovery.one,
    Result.ok_bind,Record.decode_spec,
    NativeOwnedDrop.drop,close,Result.wait_bind]
  all_goals simp only [readScript]
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (close_poll a b c d generation validGeneration)
  exact ⟨_,.refl _ _⟩

private theorem synchronized_names (selected : Names)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed (Publish.namespaceAfter true) selected = true) :
    selected = Publish.names := by
  simp [namespaceCrashAllowed,Publish.namespaceAfter,Publish.names,namedInode] at allowed
  have mapped : selected.map (fun entry => entry.1.data) =
      List.replicate selected.length Creation.path.data := by
    apply List.map_eq_replicate_iff.mpr
    intro entry member
    exact (allowed.1 entry.1 entry.2 member).symm
  rw [mapped] at unique
  rcases allowed.2 with ⟨actual,found⟩
  cases selected with
  | nil => simp at found
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
      simp at found
      simp [Publish.names,found]

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

/-- Stable single-file persistence, independently of volatile descriptors or resources. -/
private theorem stable_crash (env : Environment) (bytes : ByteArray) (script : Term)
    (snapshot : namespaceSnapshot env = some ⟨Publish.names,Publish.names,[],script⟩)
    (nodes : env.nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨bytes,bytes,0,.nil⟩)])
    (file : inode 1 env = some ⟨bytes,bytes,0,.nil⟩)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks env = some image) :
    image = ⟨Publish.names,[(1,bytes)],env.refCounter⟩ := by
  simp only [filesystemCrashImage,snapshot,
    Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at accepted
  rcases accepted with ⟨selected,table,accepted⟩
  split at accepted
  · contradiction
  · rename_i allowed
    have same := synchronized_names selected (table_unique chosen selected table) (by simpa [namespaceCrashAllowed,Publish.namespaceAfter] using allowed)
    subst selected
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
      simp only [List.mapM_cons,List.mapM_nil,Option.bind_eq_some_iff,
        file,Option.bind_some,
        List.filter_cons,List.filter_nil,Nat.reduceBEq,↓reduceIte] at accepted
      rcases accepted with ⟨images,mapped,accepted⟩
      cases saved : persist bytes bytes mask with
      | none => simp [saved,Bind.bind] at mapped
      | some actual =>
        have fixed := Publish.persist_equal_images bytes mask actual saved
        subst actual
        have image_eq : images = [(1,bytes)] := by
          simpa [saved,Bind.bind,Pure.pure] using mapped.symm
        subst images
        split at accepted
        · contradiction
        · cases accepted
          rfl

@[expose] def phaseScript : Phase → Term
  | .beforeOpen => openingScript
  | _ => .nil

private theorem phase_namespace (a b c d : U8) (generation : Nat) (phase : Phase) :
    namespaceSnapshot (phaseEnv a b c d generation phase) =
      some ⟨Publish.names,Publish.names,[],phaseScript phase⟩ := by
  cases phase <;>
    simp [phaseEnv,phaseScript,boot,scan,namespaceSnapshot,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,
      Publish.names,Publish.valid_path]

private theorem phase_inode (a b c d : U8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    inode 1 (phaseEnv a b c d generation phase) = some ⟨data a b c d,data a b c d,0,.nil⟩ := by
  have inside : ¬ generation + 1 < 1 := by omega
  have genInside : ¬ generation < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  cases phase <;>
    simp [List.filter_nil,phaseEnv,boot,scan,inode,decode,encode,limit,data_size,
      inside,genInside,genNonzero]

private theorem phase_nodes (a b c d : U8) (generation : Nat) (phase : Phase) :
    (phaseEnv a b c d generation phase).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨data a b c d,data a b c d,0,.nil⟩)] := by
  cases phase <;> simp [phaseEnv,boot,scan,inodeTypeName,namespaceTypeName,
    handleTypeName,closedHandleTypeName]

/-- Every admitted crash at every checked-reader boundary retains the committed
name and bytes. The volatile descriptor only advances the freshness mark. -/
theorem phase_crash (a b c d : U8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (phaseEnv a b c d generation phase) = some image) :
    image = ⟨Publish.names,[(1,data a b c d)],phaseWater generation phase⟩ := by
  have fixed := stable_crash _ _ _ (phase_namespace a b c d generation phase)
    (phase_nodes a b c d generation phase) (phase_inode a b c d generation validGeneration phase)
    chosen masks image accepted
  rw [fixed]
  cases phase <;> rfl

/-- Each boundary admits a concrete crash image, excluding vacuous safety. -/
theorem phase_witness (a b c d : U8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    filesystemCrashImage Publish.names [(1,⟨#[0,0,0,0]⟩)] (phaseEnv a b c d generation phase) =
      some ⟨Publish.names,[(1,data a b c d)],phaseWater generation phase⟩ := by
  simp only [filesystemCrashImage,phase_namespace a b c d generation,
    phase_nodes,Bind.bind,Option.bind_some]
  simp [Publish.names,namespaceTable,namespaceEntry,encodeNames,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,Publish.valid_path,
    phase_inode a b c d generation validGeneration,stable,Bind.bind]
  cases phase <;> rfl

theorem phase_water_valid (generation : Nat) (validGeneration : 1 ≤ generation) (phase : Phase) :
    1 ≤ phaseWater generation phase ∧ generation ≤ phaseWater generation phase := by
  cases phase <;> simp [phaseWater]
  omega

/-- Crash/restart at an actual recovery boundary preserves the value and admits
complete recovery with fresh identity. This states safety and retry capability,
not fairness or eventual success under infinitely many crashes. -/
theorem phase_retry (value : U16) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks
      (phaseEnv (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation phase) = some image) :
    (∃ residual, Result.ReadyPrefix (recover_file_record (toStr "resource"))
      (boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation) residual
      (phaseEnv (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation phase)) ∧
    restartFilesystem image openingScript =
      some (boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource") (boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) image.highWater 4 .nil true) := by
  rw [phase_crash _ _ _ _ generation validGeneration phase chosen masks image accepted]
  have valid := (phase_water_valid generation validGeneration phase).1
  exact ⟨phase_prefix _ _ _ _ generation validGeneration phase,
    restart_image _ _ _ _ _ valid,recover_value value _ valid⟩

/-- Finite sequences of admitted crashes at the actual recovery boundaries.
The next freshness mark comes from the selected filesystem image. -/
inductive CrashRetries (a b c d : U8) : Nat → Nat → Prop where
  | done (generation : Nat) : CrashRetries a b c d generation generation
  | crash (generation : Nat) (phase : Phase) (chosen : Names)
      (masks : List (Nat × ByteArray)) (image : FilesystemImage) (finalGeneration : Nat)
      (accepted : filesystemCrashImage chosen masks (phaseEnv a b c d generation phase) = some image)
      (rest : CrashRetries a b c d image.highWater finalGeneration) :
      CrashRetries a b c d generation finalGeneration

/-- Induction covers any finite number of admitted completed or interrupted
recovery attempts, preserving freshness and the actual Rust recovery result. -/
theorem finite_retries (value : U16) (generation finalGeneration : Nat)
    (trace : CrashRetries (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation finalGeneration) :
    1 ≤ generation →
    1 ≤ finalGeneration ∧ generation ≤ finalGeneration ∧
    recover_file_record (toStr "resource") (boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration 4 .nil true) := by
  induction trace with
  | done generation =>
    intro valid
    exact ⟨valid,Nat.le_refl _,recover_value value generation valid⟩
  | crash generation phase chosen masks image finalGeneration accepted rest ih =>
    intro valid
    have same := phase_crash _ _ _ _ generation valid phase chosen masks image accepted
    have progress : 1 ≤ image.highWater ∧ generation ≤ image.highWater := by
      rw [same]
      exact phase_water_valid generation valid phase
    rcases ih progress.1 with ⟨lastValid,ordered,recovered⟩
    exact ⟨lastValid,Nat.le_trans progress.2 ordered,recovered⟩

/-- Any boundary permits a nonempty finite retry trace without assuming
admission or a first-party implementation contract. -/
theorem nonempty_retry (value : U16) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    CrashRetries (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation (phaseWater generation phase) ∧
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) (phaseWater generation phase)) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) (phaseWater generation phase) 4 .nil true) := by
  have trace : CrashRetries (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation (phaseWater generation phase) :=
    .crash generation phase Publish.names [(1,⟨#[0,0,0,0]⟩)]
      ⟨Publish.names,[(1,data (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)))],phaseWater generation phase⟩ _
      (phase_witness _ _ _ _ generation validGeneration phase) (.done _)
  exact ⟨trace,(finite_retries value generation _ trace validGeneration).2.2⟩

/-- The actual resource heap after successful file and directory synchronization
has the same durable image used by checked recovery. -/
theorem committed_crash (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (Record.done env value) = some image) :
    image = ⟨Publish.names,[(1,Record.content value)],9⟩ := by
  have snapshot : namespaceSnapshot (Record.done env value) =
      some ⟨Publish.names,Publish.names,[],.nil⟩ := by
    simp [namespaceSnapshot,Record.done,Publish.committedEnv,NativeResourceArc.vmCells,
      CreatedCalls.frame,Publish.namespaceAfter,Publish.names,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,Publish.valid_path]
  have nodes : (Record.done env value).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Record.content value,Record.content value,0,.nil⟩)] := by
    simp [Record.done,Publish.committedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,Record.synced,
      inodeTypeName,closedDirectoryTypeName,namespaceTypeName,writableHandleTypeName,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName]
  have file : inode 1 (Record.done env value) =
      some ⟨Record.content value,Record.content value,0,.nil⟩ := by
    simp [inode,Record.done,Publish.committedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,Record.synced,
      inodeTypeName,closedDirectoryTypeName,namespaceTypeName,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,decode,encode,Record.content_size,limit]
  exact stable_crash _ _ _ snapshot nodes file chosen masks image accepted

/-- Any admitted post-acknowledgment image composes with any finite sequence of
crashes in actual checked recovery. No guarantee of eventual scheduling is assumed. -/
theorem committed_retries (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage) (finalGeneration : Nat)
    (accepted : filesystemCrashImage chosen masks (Record.done env value) = some image)
    (trace : CrashRetries (Record.low value) (Record.high value)
      (Record.low (~~~value)) (Record.high (~~~value)) image.highWater finalGeneration) :
    restartFilesystem image openingScript =
      some (boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration 4 .nil true) := by
  have same := committed_crash env value chosen masks image accepted
  have valid : 1 ≤ image.highWater := by rw [same]; change 1 ≤ 9; decide +kernel
  refine ⟨?_,(finite_retries value image.highWater finalGeneration trace valid).2.2⟩
  rw [same,content_layout]
  exact restart_image _ _ _ _ 9 (by decide +kernel)

/-- An actual successful NIF transaction precedes the admitted initial crash,
finite interrupted recovery trace and final recovery of the acknowledged value. -/
theorem transaction_retries (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (finalGeneration : Nat)
    (accepted : filesystemCrashImage chosen masks (Record.done env value) = some image)
    (trace : CrashRetries (Record.low value) (Record.high value)
      (Record.low (~~~value)) (Record.high (~~~value)) image.highWater finalGeneration) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool)
        (Creation.initial env Record.before.script Publish.opening) =
      (.ok Term.true,Record.done env value) ∧
    restartFilesystem image openingScript =
      some (boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) finalGeneration 4 .nil true) := by
  exact ⟨Record.create_write_commit env value registered,
    committed_retries env value chosen masks image finalGeneration accepted trace⟩

/-- A post-commit crash exists for every payload, independently of admission hypotheses. -/
theorem committed_witness (env : Environment) (value : U16) :
    filesystemCrashImage Publish.names [(1,⟨#[0,0,0,0]⟩)] (Record.done env value) =
      some ⟨Publish.names,[(1,Record.content value)],9⟩ := by
  have saved : persist (Record.content value) (Record.content value) ⟨#[0,0,0,0]⟩ =
      some (Record.content value) := by
    rw [content_layout]
    exact stable _ _ _ _
  simp [filesystemCrashImage,Record.done,Publish.committedEnv,NativeResourceArc.vmCells,
    CreatedCalls.frame,Record.synced,Publish.namespaceAfter,Publish.names,namespaceSnapshot,
    namespaceTable,namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,
    List.eraseDups_cons,tablesEqual,Publish.valid_path,namespaceCrashAllowed,namedInode,
    inode,inodeTypeName,closedDirectoryTypeName,namespaceTypeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    NativeCodec.typeName,writableHandleTypeName,decode,encode,Record.content_size,limit,saved,Bind.bind]

end FileResource.RecordRetry
