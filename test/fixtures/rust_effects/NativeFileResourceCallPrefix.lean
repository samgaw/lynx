module
public import FileResource.CommitPhases
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.CallPrefix
open NativeFile FileResource.CreatedCalls FileResource.Creation

@[expose] def invoke : Result := do
  let owner ← NativeResourceArc.decode (.nativeReference 6)
  Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool

inductive Boundary where
  | beforeDecode
  | computation (phase : CommitPhases.Phase)
  | returned

@[expose] def boundaryEnv (env : Environment) (value : U16) : Boundary → Environment
  | .beforeDecode => pinnedEnv env (Record.written value) 7 Publish.namespaceBefore
  | .computation phase => CommitPhases.phaseEnv env value phase
  | .returned => Record.done env value

/-- The actual nonfinal Rust owner release retains the independent VM pin,
committed file, namespace and closed directory capability. -/
theorem release_prefix (env : Environment) (value : U16) :
    Result.ReadyPrefix (file_resource_release ⟨3,8⟩)
      (CommitPhases.phaseEnv env value .finished) (.ok ()) (Record.done env value) := by
  have token : (CommitPhases.phaseEnv env value .finished).nativeHeap.filter (fun cell => cell.1 == 8) =
      [(8,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 3)] := by
    simp [CommitPhases.phaseEnv,Publish.directoryEnv,decodedEnv,frame,List.filter]
  have stored : (CommitPhases.phaseEnv env value .finished).nativeHeap.filter (fun cell => cell.1 == 3) =
      [(3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])] := by
    simp [CommitPhases.phaseEnv,Publish.directoryEnv,decodedEnv,frame,List.filter]
  have owners : ((CommitPhases.phaseEnv env value .finished).nativeHeap.filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType effects_native.FileResource && cell.2.2 == .nativeReference 3)).length = 2 := by
    simp [CommitPhases.phaseEnv,Publish.directoryEnv,decodedEnv,frame,List.filter,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName,closedDirectoryTypeName]
  simp only [file_resource_release,monadLift_self,NativeOwnedDrop.drop]
  have trace := NativeResourceArc.releaseOwned_retained_prefix
    (⟨3,8⟩ : NativeResourceArc effects_native.FileResource) payload _ token stored owners
  convert trace using 1
  simp [CommitPhases.phaseEnv,Publish.directoryEnv,decodedEnv,frame,Record.done,
    Publish.committedEnv,NativeResourceArc.vmCells,List.filter,List.map]

/-- The compiled facade's actual commit, owner release and Boolean return form
a complete prefix; no Rust resource owner is silently left in the terminal heap. -/
theorem facade_prefix (env : Environment) (value : U16) :
    Result.ReadyPrefix (__COMMIT__ ⟨3,8⟩) (CommitPhases.phaseEnv env value .beforeFileSync)
      (.ok true) (Record.done env value) := by
  simp only [__COMMIT__,monadLift_self]
  apply ((CommitPhases.complete_prefix env value).bind _).trans
  simp only [Result.ok_bind]
  apply ((release_prefix env value).bind _).trans
  simp only [Result.ok_bind,NativeM.ok]
  exact .refl _ _

/-- Full modeled remote invocation: decode a VM term, execute the actual compiled
Rustler facade, release its Rust owner, and encode the Elixir Boolean result. -/
theorem invocation_prefix (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix invoke (boundaryEnv env value .beforeDecode) (.ok Term.true)
      (boundaryEnv env value .returned) := by
  simp only [invoke,boundaryEnv]
  apply ((decode_prefix (ns := Publish.namespaceBefore) env (Record.written value) 7
    (by decide +kernel) registered).bind _).trans
  simp only [Result.ok_bind]
  simpa [Rustler.executeNative,Result.ok_bind,Result.handle,Rustler.encodeBool,CommitPhases.phaseEnv] using
    Rustler.executeNative_readyPrefix (facade_prefix env value) Rustler.encodeBool

/-- Decode/release boundaries join the existing native I/O boundaries, each
with its actual remaining computation. -/
theorem boundary_prefix (env : Environment) (value : U16) (boundary : Boundary)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    ∃ residual, Result.ReadyPrefix invoke (boundaryEnv env value .beforeDecode)
      residual (boundaryEnv env value boundary) := by
  cases boundary with
  | beforeDecode => exact ⟨_,.refl _ _⟩
  | returned => exact ⟨.ok Term.true,invocation_prefix env value registered⟩
  | computation phase =>
    obtain ⟨remaining,trace⟩ := CommitPhases.nif_phase_prefix env value phase
    refine ⟨remaining,?_⟩
    simp only [invoke,boundaryEnv]
    apply ((decode_prefix (ns := Publish.namespaceBefore) env (Record.written value) 7
      (by decide +kernel) registered).bind _).trans
    simpa only [Result.ok_bind,CommitPhases.phaseEnv,Nat.reduceAdd] using trace

/-- The complete prefix supplies the ordinary invocation equation in a
caller's current heap, without requiring the caller to unfold resource internals. -/
theorem call_run (value : U16) (env : Environment) (counter : env.nativeRefCounter = 7)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++
      frame (Record.written value) Publish.namespaceBefore)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) env =
      (.ok Term.true,Record.done env value) := by
  have trace := (invocation_prefix env value registered).apply
  simpa only [invoke,boundaryEnv,pinnedEnv,← heap,← counter,Result.ok_apply] using trace

/-- Every admitted persistent image at every full invocation boundary composes
with actual checked Rust recovery, including before decode and after release. -/
theorem boundary_recovery (env : Environment) (value : U16) (boundary : Boundary)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value boundary) = some image) :
    (∃ residual, Result.ReadyPrefix invoke (boundaryEnv env value .beforeDecode)
      residual (boundaryEnv env value boundary)) ∧
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  refine ⟨boundary_prefix env value boundary registered,?_⟩
  cases boundary with
  | beforeDecode => exact ShortRecovery.all_image_recovery env value chosen masks image error accepted
  | computation phase => exact (CommitPhases.phase_recovery env value phase chosen masks image error accepted).2
  | returned =>
    have fixed := RecordRetry.committed_crash env value chosen masks image accepted
    refine ⟨RecordRecovery.openingScript,
      RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) 9,
      RecordRecovery.scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) 9 4 .nil true,
      .Ok (some value),?_,RecordRecovery.recover_value value 9 (by decide +kernel),Or.inr (Or.inr rfl)⟩
    rw [fixed,RecordRecovery.content_layout]
    exact RecordRecovery.restart_image _ _ _ _ 9 (by decide +kernel)

/-- Acknowledged invocation composes with every finite supported mixed recovery
trace after any admitted crash of its terminal state. -/
theorem acknowledged_retries (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
    (accepted : filesystemCrashImage chosen masks (boundaryEnv env value .returned) = some image)
    (trace : RecordErrors.Attempts value image.highWater last) :
    Result.ReadyPrefix invoke (boundaryEnv env value .beforeDecode) (.ok Term.true)
      (boundaryEnv env value .returned) ∧
    restartFilesystem image RecordRecovery.openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last) =
      (.ok (.Ok (some value)),RecordRecovery.scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last 4 .nil true) := by
  exact ⟨invocation_prefix env value registered,
    RecordErrors.committed_attempts env value chosen masks image last accepted trace⟩

@[expose] def boundaryWater : Boundary → Nat
  | .beforeDecode => 7
  | .computation phase => CommitPhases.phaseWater phase
  | .returned => 9

/-- Every decoder, native and release boundary is reachable and admits a concrete
full-content image, independently of any crash-admission hypothesis. -/
theorem boundary_witness (env : Environment) (value : U16) (boundary : Boundary)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (∃ residual, Result.ReadyPrefix invoke (boundaryEnv env value .beforeDecode)
      residual (boundaryEnv env value boundary)) ∧
    ∃ mask, filesystemCrashImage Publish.names [(1,mask)] (boundaryEnv env value boundary) =
      some ⟨Publish.names,[(1,Record.content value)],boundaryWater boundary⟩ := by
  refine ⟨boundary_prefix env value boundary registered,?_⟩
  cases boundary with
  | beforeDecode =>
    refine ⟨RecordRecovery.tearingMask true true true true,?_⟩
    simpa [boundaryEnv,boundaryWater,RecordRecovery.tornData,Record.selected,RecordRecovery.content_layout] using
      RecordRecovery.written_image env value true true true true
  | computation phase => exact ⟨_,(CommitPhases.phase_witness env value phase).2⟩
  | returned => exact ⟨_,RecordRetry.committed_witness env value⟩

/-- Registration admission is supplied from the compiled Rustler configuration;
it changes no file, resource ownership or identity watermark. -/
@[expose] def registeredEnv (env : Environment) : Environment :=
  {env with nativeResourceTypes :=
    (env.nativeResourceTypes ++ [NativeResourceArc.typeName effects_native.FileResource]).eraseDups}
@[expose] def registered_invoke : Result :=
  Rustler.withResourceTypes [NativeResourceArc.typeName effects_native.FileResource] invoke

/-- Include the adapter's registration admission before decoding the VM term. -/
theorem registered_prefix (env : Environment) (value : U16) :
    Result.ReadyPrefix registered_invoke (boundaryEnv env value .beforeDecode) (.ok Term.true)
      (Record.done (registeredEnv env) value) := by
  unfold registered_invoke Rustler.withResourceTypes
  apply Result.ReadyPrefix.nativeGet
  apply Result.ReadyPrefix.nativeSet
  have registered : NativeResourceArc.typeName effects_native.FileResource ∈
      (registeredEnv env).nativeResourceTypes := by simp [registeredEnv]
  simpa [registeredEnv,boundaryEnv,pinnedEnv] using invocation_prefix (registeredEnv env) value registered

end FileResource.CallPrefix
