module
public import FileResource.Creation
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.CreatedCalls
open NativeFile FileResource.Creation

@[expose] def Valid (state : State) : Prop :=
  state.visible.size ≤ limit ∧ state.durable.size ≤ limit ∧ state.position ≤ limit

@[expose] def pendingNamespace : NamespaceSnapshot := ⟨[(path,1)],[],[[(path,1)]],.nil⟩

@[expose] def frame (state : State) (ns : NamespaceSnapshot := pendingNamespace) : List (Nat × String × Term) := [
  (2,writableHandleTypeName,encodeHandle ⟨1,state.position,state.script⟩),
  (1,inodeTypeName,encode {state with position := 0,script := .nil}),
  (0,namespaceTypeName,encodeNamespace ns)]

@[expose] def pinnedEnv (env : Environment) (state : State) (counter : Nat) (ns : NamespaceSnapshot := pendingNamespace) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := NativeResourceArc.vmCells payload 3 5 6 ++ frame state ns}

@[expose] def decodedEnv (env : Environment) (state : State) (counter : Nat) (ns : NamespaceSnapshot := pendingNamespace) : Environment :=
  {env with nativeRefCounter := counter + 1, nativeHeap := [
    (counter + 1,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 3),
    (6,NativeResourceArc.termType effects_native.FileResource,.tuple #[.nativeReference 3,.nativeReference 5]),
    (5,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 3),
    (3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])] ++ frame state ns}

theorem pin {ns : NamespaceSnapshot} (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    NativeResourceArc.Pinned payload 3 5 6 (pinnedEnv env state counter ns) := by
  constructor
  · simp [pinnedEnv,bounded]
  · intro cell member
    simp only [pinnedEnv,NativeResourceArc.vmCells,frame,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [pinnedEnv] <;> omega
  · simp [pinnedEnv,NativeResourceArc.vmCells,frame]
  · simp [pinnedEnv,NativeResourceArc.vmCells,frame]
  · simp [pinnedEnv,NativeResourceArc.vmCells,frame]
  · simp [pinnedEnv,NativeResourceArc.vmCells,frame,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
      writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem decode_next {ns : NamespaceSnapshot} {α : Type} (env : Environment) (state : State) (counter : Nat)
    (bounded : 6 ≤ counter) (next : NativeResourceArc effects_native.FileResource → NativeM α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (NativeResourceArc.decode (.nativeReference 6) >>= next) (pinnedEnv env state counter ns) =
      next ⟨3,counter + 1⟩ (decodedEnv env state counter ns) := by
  simpa [pinnedEnv,decodedEnv,NativeResourceArc.vmCells,frame,List.map] using
    NativeResourceArc.decode_pinned_next payload next (pinnedEnv env state counter ns)
      3 5 6 (pin (ns := ns) env state counter bounded) registered

/-- Successful VM-term decoding retains its actual lookup and owner-allocation prefix. -/
theorem decode_prefix {ns : NamespaceSnapshot} (env : Environment) (state : State) (counter : Nat)
    (bounded : 6 ≤ counter)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6)) (pinnedEnv env state counter ns)
      (.ok (⟨3,counter + 1⟩ : NativeResourceArc effects_native.FileResource))
      (decodedEnv env state counter ns) := by
  simpa [pinnedEnv,decodedEnv,NativeResourceArc.vmCells,frame,List.map] using
    NativeResourceArc.decode_pinned_prefix payload (pinnedEnv env state counter ns)
      3 5 6 (pin (ns := ns) env state counter bounded) registered

private theorem decoded_views {ns : NamespaceSnapshot} (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter) :
    (decodedEnv env state counter ns).nativeHeap.filter (fun cell => cell.1 == counter + 1) =
      [(counter + 1,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 3)] ∧
    (decodedEnv env state counter ns).nativeHeap.filter (fun cell => cell.1 == 3) =
      [(3,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])] ∧
    ((decodedEnv env state counter ns).nativeHeap.filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType effects_native.FileResource && cell.2.2 == .nativeReference 3)).length = 2 := by
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have b2 : (counter == 2) = false := by simp; omega
  have b4 : (counter == 4) = false := by simp; omega
  have b5 : (counter == 5) = false := by simp; omega
  simp [decodedEnv,frame,List.filter,b0,b1,b2,b4,b5,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,
    writableHandleTypeName,inodeTypeName,namespaceTypeName]

private theorem retained_release {ns : NamespaceSnapshot} {α β : Type} (env : Environment) (state : State) (counter : Nat)
    (bounded : 6 ≤ counter) (finish : Result α) (handler : Exception → Result α)
    (next : α → Result β) :
    ((Result.handle (do NativeResourceArc.releaseOwned (⟨3,counter + 1⟩ : NativeResourceArc effects_native.FileResource); finish) handler) >>= next)
      (decodedEnv env state counter ns) =
    ((Result.handle finish handler) >>= next) (pinnedEnv env state (counter + 1) ns) := by
  obtain ⟨token,stored,owners⟩ := decoded_views (ns := ns) env state counter bounded
  rw [NativeResourceArc.releaseOwned_retained_handled_next _ payload _ _ _ _ token stored owners]
  have n0 : (counter != 0) = true := by simp; omega
  have n1 : (counter != 1) = true := by simp; omega
  have n2 : (counter != 2) = true := by simp; omega
  have n4 : (counter != 4) = true := by simp; omega
  have n5 : (counter != 5) = true := by simp; omega
  congr 1
  simp [decodedEnv,pinnedEnv,NativeResourceArc.vmCells,frame,List.filter,List.map,n0,n1,n2,n4,n5]

/-- Decode and borrow a VM-pinned resource before an arbitrary effectful continuation.
The continuation retains its Rust owner, including across further allocations. -/
theorem borrowed_next {ns : NamespaceSnapshot} {α β : Type}
    (env : Environment) (state : State) (counter : Nat) (bounded : 6 ≤ counter)
    (finish : NativeResourceArc effects_native.FileResource → effects_native.FileResource → NativeM α)
    (handler : Exception → NativeM α) (next : α → NativeM β)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Result.handle (do
        let resource ← NativeResourceArc.deref owner
        finish owner resource) handler
      next result) (pinnedEnv env state counter ns) =
    ((Result.handle (finish ⟨3,counter + 1⟩ payload) handler) >>= next)
      (decodedEnv env state counter ns) := by
  rw [decode_next (ns := ns) env state counter bounded _ registered]
  obtain ⟨token,stored,owners⟩ := decoded_views (ns := ns) env state counter bounded
  exact NativeResourceArc.deref_retained_handled_next _ payload _ _ _ _ token stored owners

/-- Transport a ready native effect through decoding, shared dereference and owned release. -/
theorem retained_effect_next {ns : NamespaceSnapshot} {α β γ : Type} (env : Environment) (before after : State)
    (counter : Nat) (bounded : 6 ≤ counter) (body : effects_native.FileResource → NativeM α)
    (reply : α) (finish : α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes)
    (trace : Result.ReadyPrefix (body payload) (decodedEnv env before counter ns)
      (.ok reply) (decodedEnv env after counter ns)) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Result.handle (do
        let resource ← NativeResourceArc.deref owner
        let value ← body resource
        NativeResourceArc.releaseOwned owner
        finish value) handler
      next result) (pinnedEnv env before counter ns) =
    ((Result.handle (finish reply) handler) >>= next) (pinnedEnv env after (counter + 1) ns) := by
  rw [decode_next (ns := ns) env before counter bounded _ registered]
  obtain ⟨token,stored,owners⟩ := decoded_views (ns := ns) env before counter bounded
  rw [NativeResourceArc.deref_retained_handled_next _ payload _ _ _ _ token stored owners]
  rw [(((trace.bind (fun value => do
    NativeResourceArc.releaseOwned (⟨3,counter + 1⟩ : NativeResourceArc effects_native.FileResource)
    finish value)).handle handler).bind next).apply]
  simp only [Result.ok_bind]
  exact retained_release (ns := ns) env after counter bounded (finish reply) handler next

/-- Releasing a decoded owner retains the newly created resource's VM pin (ns := ns) and inode. -/
theorem release_next {ns : NamespaceSnapshot} {α : Type} (env : Environment) (state : State) (counter : Nat)
    (bounded : 6 ≤ counter) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])
      next result) (pinnedEnv env state counter ns) =
      next (.tuple #[]) (pinnedEnv env state (counter + 1) ns) := by
  rw [decode_next (ns := ns) env state counter bounded _ registered]
  simp only [__RELEASE__,file_resource_release,monadLift_self,NativeOwnedDrop.drop,Rustler.executeNative]
  have released := retained_release (ns := ns) env state counter bounded (Result.ok (Term.tuple #[]))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted) next
  convert released using 1 <;> try simp [Result.handle]
  all_goals congr 1


private theorem lookup_decoded {ns : NamespaceSnapshot} (env : Environment) (state : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid state) :
    lookup ⟨2⟩ (decodedEnv env state counter ns) = some state := by
  obtain ⟨visible,durable,position⟩ := valid
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have live : 1 ≤ counter := by omega
  have nonzero : counter ≠ 0 := by omega
  have nonnegative : ¬ (state.position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  simp [live,nonzero,nonnegative,lookup,decodedEnv,frame,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,
    decode,encode,not_lt.mpr visible,not_lt.mpr durable,not_lt.mpr position,
    b0,b1,writableHandleTypeName,typeName,inodeTypeName,
    not_lt.mpr (Int.natCast_nonneg limit)]

private theorem store_decoded {ns : NamespaceSnapshot} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid before) :
    store ⟨2⟩ after (decodedEnv env before counter ns) = decodedEnv env after counter ns := by
  obtain ⟨_,_,position⟩ := valid
  have b1 : (counter == 1) = false := by simp; omega
  have nonzero : counter ≠ 0 := by omega
  have nonnegative : ¬ (before.position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  simp [nonzero,nonnegative,store,decodedEnv,frame,decodeHandle,encodeHandle,sharedStore,
    not_lt.mpr position,b1,writableHandleTypeName,typeName]
  omega

/-- A shared writable handle follows the same bounded write transition as the inode model. -/
theorem write_poll {ns : NamespaceSnapshot} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid before) (data : Slice U8)
    (ready : blocked before = false) (reply : core.result.Result Usize NativeIoError)
    (step : writeStep before data = some (reply,after)) :
    pollWrite ⟨2⟩ data (decodedEnv env before counter ns) =
      some (.ok (reply,⟨2⟩),decodedEnv env after counter ns) := by
  have not_read : getHandle ⟨2⟩ handleTypeName (decodedEnv env before counter ns) = none := by
    have b1 : (counter == 1) = false := by simp; omega
    simp [getHandle,decodedEnv,frame,b1,handleTypeName,writableHandleTypeName]
  simp only [pollWrite,lookup_decoded (ns := ns) env before counter bounded valid,ready,
    Bool.false_eq_true,↓reduceIte,step,not_read,store_decoded (ns := ns) env before after counter bounded valid]

/-- File synchronization preserves the caller's declared namespace state. -/
theorem file_sync_poll {ns : NamespaceSnapshot} (env : Environment) (before after : State)
    (counter : Nat) (bounded : 6 ≤ counter) (valid : Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (),after)) :
    pollSync ⟨2⟩ (decodedEnv env before counter ns) =
      some (.ok (.Ok ()),decodedEnv env after counter ns) := by
  simp [pollSync,lookup_decoded (ns := ns) env before counter bounded valid,ready,step,
    store_decoded (ns := ns) env before after counter bounded valid]

/-- Sync acts on the newly created handle and shared inode while its decoded owner is live. -/
theorem sync_next {ns : NamespaceSnapshot} {α : Type} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (),after)) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__SYNC__ owner) Rustler.encodeBool
      next result) (pinnedEnv env before counter ns) =
    next Term.true (pinnedEnv env after (counter + 1) ns) := by
  rw [decode_next (ns := ns) env before counter bounded _ registered]
  simp only [__SYNC__,file_resource_sync,monadLift_self,Rustler.executeNative,bind_assoc]
  obtain ⟨token,stored,owners⟩ := decoded_views (ns := ns) env before counter bounded
  rw [NativeResourceArc.deref_retained_handled_next _ payload _ _ _ _ token stored owners]
  have poll : pollSync ⟨2⟩ (decodedEnv env before counter ns) =
      some (.ok (.Ok ()),decodedEnv env after counter ns) := by
    simp [pollSync,lookup_decoded (ns := ns) env before counter bounded valid,ready,step,
      store_decoded (ns := ns) env before after counter bounded valid]
  simp only [payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind,
    Result.handle]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp only [Result.ok_bind,monadLift_self,file_resource_release,NativeOwnedDrop.drop,NativeM.ok]
  have released := retained_release (ns := ns) env after counter bounded (Result.ok Term.true)
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted) next
  convert released using 1 <;> try simp [Result.handle,Rustler.encodeBool]
  all_goals congr 1


theorem release_env {ns : NamespaceSnapshot} {α : Type} (state : State) (next : Term → Result α) (env : Environment)
    (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame state ns)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])
      next result) env = next (.tuple #[]) {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  simpa only [pinnedEnv,← heap] using release_next (ns := ns) env state env.nativeRefCounter bounded next registered

theorem sync_env {ns : NamespaceSnapshot} {α : Type} (before after : State) (valid : Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (),after))
    (next : Term → Result α) (env : Environment) (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame before ns)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__SYNC__ owner) Rustler.encodeBool
      next result) env = next Term.true (pinnedEnv env after (env.nativeRefCounter + 1) ns) := by
  simpa only [pinnedEnv,← heap] using
    sync_next (ns := ns) env before after env.nativeRefCounter bounded valid ready step next registered

theorem sync_run {ns : NamespaceSnapshot} (before after : State) (valid : Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (),after))
    (env : Environment) (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame before ns)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__SYNC__ owner) Rustler.encodeBool) env =
        (.ok Term.true,pinnedEnv env after (env.nativeRefCounter + 1) ns) := by
  simpa only [Result.bind_ok,Result.ok_apply] using
    sync_env (ns := ns) before after valid ready step Result.ok env bounded heap registered

@[expose] def syncChoice (rest : Term) : Term :=
  .cons (.tuple #[.atom "sync_all",.atom "ok",.integer 0,.bitstring ByteArray.empty 0]) rest
@[expose] def before : State := ⟨ByteArray.empty,ByteArray.empty,0,syncChoice (syncChoice .nil)⟩
@[expose] def once : State := ⟨ByteArray.empty,ByteArray.empty,0,syncChoice .nil⟩
@[expose] def twice : State := ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩
@[expose] def seed : Environment := initial {} before.script

theorem before_valid : Valid before := by simp [Valid,before,limit,← ByteArray.size_data]
theorem once_valid : Valid once := by simp [Valid,once,limit,← ByteArray.size_data]
theorem before_ready : blocked before = false := rfl
theorem once_ready : blocked once = false := rfl
theorem first_step : syncStep before = some (.Ok (),once) := by simp [syncStep,before,once,syncChoice,action]
theorem second_step : syncStep once = some (.Ok (),twice) := by simp [syncStep,once,twice,syncChoice,action]

theorem returned_before (env : Environment) : returned env before.script = pinnedEnv env before 6 := rfl

/-- Both native calls operate on the actual newly allocated resource, not an admitted handle. -/
theorem create_release_sync (env : Environment)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__SYNC__ owner) Rustler.encodeBool) (initial env before.script) =
      (.ok Term.true,pinnedEnv env once 8) := by
  rw [create_next (rest := .nil) env before.script _ registered,returned_before]
  rw [release_next (ns := pendingNamespace) env before 6 (by omega) _ registered]
  exact sync_run (ns := pendingNamespace) before once before_valid before_ready first_step _ (by simp [pinnedEnv]) rfl registered

end FileResource.CreatedCalls
