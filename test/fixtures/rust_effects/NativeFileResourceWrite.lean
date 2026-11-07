module
public import FileResource.CreatedCalls
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Write
open NativeFile FileResource.Creation FileResource.CreatedCalls

@[expose] def wire (value : U16) : Slice U8 := Array.to_slice (core.num.U16.to_le_bytes value)
@[expose] def content (value : U16) : ByteArray := bytes (wire value)

theorem wire_length (value : U16) : (wire value).val.length = 2 := by
  simp [wire]

theorem content_size (value : U16) : (content value).size = 2 := by
  simpa [content,bytes,← ByteArray.size_data] using wire_length value


/-- The actual facade reports complete versus partial writes while retaining its VM-held file. -/
theorem write_next {ns : NamespaceSnapshot} {α : Type} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (value : U16) (count : Usize)
    (step : writeStep before (wire value) = some (.Ok count,after))
    (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      let result ← Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool
      next result) (pinnedEnv env before counter ns) =
    next (Rustler.encodeBool (count = 2#usize)) (pinnedEnv env after (counter + 1) ns) := by
  have trace : Result.ReadyPrefix (effects_core.write_shared_file payload.file (wire value))
      (decodedEnv env before counter ns) (.ok (.Ok count)) (decodedEnv env after counter ns) := by
    simp only [effects_core.write_shared_file,monadLift_self,write,Result.wait_bind,payload]
    apply Result.ReadyPrefix.wait _ _ (.ok (.Ok count,⟨2⟩)) _ _ _ _
      (write_poll (ns := ns) env before after counter bounded valid (wire value) ready (.Ok count) step)
    simpa [NativeM.ok] using Result.ReadyPrefix.refl
      (Result.ok (.Ok count : core.result.Result Usize NativeIoError)) (decodedEnv env after counter ns)
  let finish := fun outcome : core.result.Result Usize NativeIoError => do
    let result : Bool ← match outcome with
      | .Ok written => NativeM.ok (written = Slice.len (wire value))
      | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false
    Result.ok (Rustler.encodeBool result)
  let handler : Exception → Result Term := fun error => match error with
    | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
    | _ => Result.error .exhausted
  have result := retained_effect_next (ns := ns) env before after counter bounded
    (fun resource => effects_core.write_shared_file resource.file (wire value))
    (.Ok count) finish handler next registered trace
  have length : Slice.len (wire value) = 2#usize := by
    apply UScalar.eq_of_val_eq
    simp [Slice.len,wire_length]
  have compiled (owner : NativeResourceArc effects_native.FileResource) :
      (do let result ← __WRITE__ owner value; Result.ok (Rustler.encodeBool result)) =
      (do
        let resource ← NativeResourceArc.deref owner
        let outcome ← effects_core.write_shared_file resource.file (wire value)
        NativeResourceArc.releaseOwned owner
        finish outcome) := by
    simp only [__WRITE__,file_resource_write,file_resource_release,
      monadLift_self,NativeM.lift,NativeM.ok,Result.ok_bind,wire,bind_assoc,NativeOwnedDrop.drop]
    congr 1
    funext resource
    congr 1
    funext outcome
    congr 1
    funext ignored
    cases outcome <;> simp [finish,NativeM.ok,wire,NativeOwnedDrop.drop,bind_assoc]
    all_goals rfl
  simp only [Rustler.executeNative,compiled]
  convert result using 1 <;> simp [finish,handler,NativeM.ok,length,Result.handle]
  all_goals rfl


/-- The verified write contract applies in an ordinary caller's current environment. -/
theorem write_env {ns : NamespaceSnapshot} {α : Type} (before after : State) (valid : Valid before)
    (ready : blocked before = false) (value : U16) (count : Usize)
    (step : writeStep before (wire value) = some (.Ok count,after)) (next : Term → Result α)
    (env : Environment) (bounded : 6 ≤ env.refCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame before ns)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      let result ← Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool
      next result) env = next (Rustler.encodeBool (count = 2#usize))
        (pinnedEnv env after (env.refCounter + 1) ns) := by
  simpa only [pinnedEnv,← heap] using
    write_next (ns := ns) env before after env.refCounter bounded valid ready value count step next registered

@[expose] def writeChoice (count : Nat) : Term :=
  .cons (.tuple #[.atom "write",.atom "ok",.integer count,.bitstring ByteArray.empty 0]) (syncChoice .nil)
@[expose] def before : State := ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2⟩
@[expose] def written (value : U16) : State := ⟨content value,ByteArray.empty,2,syncChoice .nil⟩
@[expose] def synced (value : U16) : State := ⟨content value,content value,2,.nil⟩
@[expose] def seed : Environment := initial {} before.script

theorem before_valid : Valid before := by simp [Valid,before,limit,← ByteArray.size_data]
theorem written_valid (value : U16) : Valid (written value) := by
  simp only [Valid,written,content_size]
  simp [limit,← ByteArray.size_data]
theorem before_ready : blocked before = false := rfl
theorem written_ready (value : U16) : blocked (written value) = false := rfl

theorem full_step (value : U16) : writeStep before (wire value) = some (.Ok 2#usize,written value) := by
  have take : (bytes (wire value)).data.toList.take 2 = (bytes (wire value)).data.toList := by
    apply List.take_of_length_le
    have size : (bytes (wire value)).data.toList.length = 2 := by
      simpa [content,← ByteArray.size_data] using content_size value
    omega
  simp [writeStep,before,written,writeChoice,action,wire_length,limit,
    overwrite,persist,take,content,← ByteArray.size_data]
  constructor
  · apply UScalar.eq_of_val_eq; rfl
  · rfl

theorem sync_step (value : U16) : syncStep (written value) = some (.Ok (),synced value) := by
  simp [syncStep,written,synced,syncChoice,action]

theorem returned_before (env : Environment) : returned env before.script = pinnedEnv env before 6 := rfl

/-- Both bytes become durable only after the actual cross-crate synchronization call. -/
theorem create_write_sync (env : Environment) (value : U16)
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
      Rustler.executeNative (__SYNC__ owner) Rustler.encodeBool) (initial env before.script) =
      (.ok Term.true,pinnedEnv env (synced value) 8) ∧
    (written value).durable = ByteArray.empty ∧
    (synced value).durable = content value ∧ (synced value).durable.size = 2 := by
  constructor
  · rw [create_next (rest := .nil) env before.script _ registered,returned_before]
    rw [write_next (ns := pendingNamespace) env before (written value) 6 (by omega) before_valid before_ready value 2#usize
      (full_step value) _ registered]
    exact sync_run (ns := pendingNamespace) (written value) (synced value) (written_valid value) (written_ready value)
      (sync_step value) _ (by simp [pinnedEnv]) rfl registered
  · simp [written,synced,content_size]

@[expose] def partialBefore : State := ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 1⟩
@[expose] def partialWritten (value : U16) : State :=
  ⟨overwrite ByteArray.empty 0 (content value) 1,ByteArray.empty,1,syncChoice .nil⟩

theorem partial_step (value : U16) :
    writeStep partialBefore (wire value) = some (.Ok 1#usize,partialWritten value) := by
  simp [writeStep,partialBefore,partialWritten,writeChoice,action,wire_length,
    limit,persist,content,← ByteArray.size_data]
  constructor
  · apply UScalar.eq_of_val_eq; rfl
  · rfl

/-- A real short write changes visible file state but is never acknowledged as complete. -/
theorem short_not_acknowledged (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool) (initial env partialBefore.script) =
      (.ok Term.false,pinnedEnv env (partialWritten value) 7) := by
  rw [create_next (rest := .nil) env partialBefore.script _ registered]
  change (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool)
    (pinnedEnv env partialBefore 6) = _
  have valid : Valid partialBefore := by simp [Valid,partialBefore,limit,← ByteArray.size_data]
  simpa [Result.bind_ok,Result.ok_apply,Rustler.encodeBool] using
    write_next (ns := pendingNamespace) env partialBefore (partialWritten value) 6 (by omega) valid rfl value 1#usize
      (partial_step value) Result.ok registered

end FileResource.Write
