module
public import FileResource.NifProperties
public import FileResource.Properties
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Calls
open FileResource.Properties NativeFile

@[expose] def pinnedEnv (env : Environment) (state : State) (counter : Nat) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := NativeResourceArc.vmCells payload 2 4 5 ++ [fileCell state]}

@[expose] def decodedEnv (env : Environment) (state : State) (counter : Nat) : Environment :=
  {env with nativeRefCounter := counter + 1, nativeHeap := [
    (counter + 1,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 2),
    (5,NativeResourceArc.termType effects_native.FileResource,.tuple #[.nativeReference 2,.nativeReference 4]),
    (4,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 2),
    (2,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload]),fileCell state]}

theorem pin (env : Environment) (state : State) (counter : Nat) (bounded : 5 ≤ counter) :
    NativeResourceArc.Pinned payload 2 4 5 (pinnedEnv env state counter) := by
  constructor
  · simp [pinnedEnv,bounded]
  · intro cell member
    simp only [pinnedEnv,NativeResourceArc.vmCells,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [pinnedEnv,fileCell] <;> omega
  · simp [pinnedEnv,NativeResourceArc.vmCells,fileCell]
  · simp [pinnedEnv,NativeResourceArc.vmCells,fileCell]
  · simp [pinnedEnv,NativeResourceArc.vmCells,fileCell]
  · simp [pinnedEnv,NativeResourceArc.vmCells,fileCell,NativeFile.encode,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType]

theorem decode_next {α : Type} (env : Environment) (state : State) (counter : Nat)
    (bounded : 5 ≤ counter) (next : NativeResourceArc effects_native.FileResource → NativeM α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (NativeResourceArc.decode (.nativeReference 5) >>= next) (pinnedEnv env state counter) =
      next ⟨2,counter + 1⟩ (decodedEnv env state counter) := by
  have decoded := NativeResourceArc.decode_pinned_next payload next (pinnedEnv env state counter)
    2 4 5 (pin env state counter bounded) registered
  simpa [pinnedEnv,decodedEnv,NativeResourceArc.vmCells,fileCell,List.map] using decoded


private theorem decoded_views (env : Environment) (state : State) (counter : Nat) (bounded : 5 ≤ counter) :
    (decodedEnv env state counter).nativeHeap.filter (fun cell => cell.1 == counter + 1) =
      [(counter + 1,NativeResourceArc.handleType effects_native.FileResource,.nativeReference 2)] ∧
    (decodedEnv env state counter).nativeHeap.filter (fun cell => cell.1 == 2) =
      [(2,NativeResourceArc.typeName effects_native.FileResource,.tuple #[.integer 2,NativeCodec.encode payload])] ∧
    ((decodedEnv env state counter).nativeHeap.filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType effects_native.FileResource && cell.2.2 == .nativeReference 2)).length = 2 := by
  have b0 : (counter == 0) = false := by simp; omega
  have b1 : (counter == 1) = false := by simp; omega
  have b3 : (counter == 3) = false := by simp; omega
  have b4 : (counter == 4) = false := by simp; omega
  simp [decodedEnv,fileCell,List.filter,b0,b1,b3,b4,NativeFile.encode,NativeFile.typeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType]

private theorem retained_release {α β : Type} (env : Environment) (state : State) (counter : Nat)
    (bounded : 5 ≤ counter) (finish : Result α) (handler : Exception → Result α)
    (next : α → Result β) :
    ((Result.handle (do NativeResourceArc.releaseOwned (⟨2,counter + 1⟩ : NativeResourceArc effects_native.FileResource); finish) handler) >>= next)
      (decodedEnv env state counter) =
    ((Result.handle finish handler) >>= next) (pinnedEnv env state (counter + 1)) := by
  obtain ⟨token,stored,owners⟩ := decoded_views env state counter bounded
  rw [NativeResourceArc.releaseOwned_retained_handled_next _ payload _ _ _ _ token stored owners]
  have n0 : (counter != 0) = true := by simp; omega
  have n1 : (counter != 1) = true := by simp; omega
  have n3 : (counter != 3) = true := by simp; omega
  have n4 : (counter != 4) = true := by simp; omega
  congr 1
  simp [decodedEnv,pinnedEnv,NativeResourceArc.vmCells,fileCell,List.filter,List.map,n0,n1,n3,n4]

/-- Repeated native calls advance fresh identities without consuming the VM pin. -/
theorem release_next {α : Type} (env : Environment) (state : State) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let result ← Rustler.executeNative
        (__RELEASE__ owner)
        (fun _ => .tuple #[])
      next result) (pinnedEnv env state counter) =
      next (.tuple #[]) (pinnedEnv env state (counter + 1)) := by
  rw [decode_next env state counter bounded _ registered]
  simp only [__RELEASE__,
    file_resource_release,monadLift_self,NativeOwnedDrop.drop,Rustler.executeNative]
  have released := retained_release env state counter bounded (Result.ok (Term.tuple #[]))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted) next
  convert released using 1 <;> try simp [Result.handle]
  all_goals congr 1



/-- Synchronization follows the actual core implementation while the decoded owner is live. -/
theorem sync_next {α : Type} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 5 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (),after)) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let result ← Rustler.executeNative
        (__SYNC__ owner)
        Rustler.encodeBool
      next result) (pinnedEnv env before counter) =
    next Term.true (pinnedEnv env after (counter + 1)) := by
  rw [decode_next env before counter bounded _ registered]
  simp only [__SYNC__,
    file_resource_sync,monadLift_self,Rustler.executeNative,bind_assoc]
  obtain ⟨token,stored,owners⟩ := decoded_views env before counter bounded
  simp only [NativeResourceArc.deref_retained_handled_next (⟨2,counter+1⟩ : NativeResourceArc effects_native.FileResource) payload _ _ next (decodedEnv env before counter) token stored owners]
  have zero : counter ≠ 0 := by omega
  have poll : pollSync ⟨1⟩ (decodedEnv env before counter) =
      some (.ok (.Ok ()),decodedEnv env after counter) := by
    simp [pollSync,lookup,decodedEnv,fileCell,decode_valid before valid,ready,step,store,zero]
  simp only [payload,effects_core.synchronize_file,monadLift_self,syncAll,Result.wait_bind,
    Result.handle]
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp only [Result.ok_bind,monadLift_self,file_resource_release,NativeOwnedDrop.drop,
    NativeM.ok]
  have released := retained_release env after counter bounded (Result.ok Term.true)
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted) next
  convert released using 1 <;> try simp [Result.handle,Rustler.encodeBool]
  all_goals congr 1

/-- The retained-call contract is independent of the caller's other runtime fields. -/
theorem release_env {α : Type} (state : State) (next : Term → Result α) (env : Environment)
    (bounded : 5 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [fileCell state])
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let result ← Rustler.executeNative
        (__RELEASE__ owner)
        (fun _ => .tuple #[])
      next result) env = next (.tuple #[]) {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  simpa only [pinnedEnv,← heap] using release_next env state env.nativeRefCounter bounded next registered

theorem sync_env {α : Type} (before after : State) (valid : Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (),after))
    (next : Term → Result α) (env : Environment) (bounded : 5 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [fileCell before])
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let result ← Rustler.executeNative
        (__SYNC__ owner)
        Rustler.encodeBool
      next result) env = next Term.true (pinnedEnv env after (env.nativeRefCounter + 1)) := by
  simpa only [pinnedEnv,← heap] using
    sync_next env before after env.nativeRefCounter bounded valid ready step next registered

theorem sync_run (before after : State) (valid : Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (),after))
    (env : Environment) (bounded : 5 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [fileCell before])
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      Rustler.executeNative
        (__SYNC__ owner)
        Rustler.encodeBool) env = (.ok Term.true,pinnedEnv env after (env.nativeRefCounter + 1)) := by
  simpa only [Result.bind_ok,Result.ok_apply] using
    sync_env before after valid ready step Result.ok env bounded heap registered

@[expose] def syncChoice (rest : Term) : Term :=
  .cons (.tuple #[.atom "sync_all",.atom "ok",.integer 0,.bitstring ByteArray.empty 0]) rest
@[expose] def before : State := ⟨⟨#[2]⟩,⟨#[1]⟩,0,syncChoice (syncChoice closeChoice)⟩
@[expose] def once : State := ⟨⟨#[2]⟩,⟨#[2]⟩,0,syncChoice closeChoice⟩
@[expose] def twice : State := ⟨⟨#[2]⟩,⟨#[2]⟩,0,closeChoice⟩
@[expose] def seed : Environment :=
  pinnedEnv (({} : Environment).setPdict [(.atom "file",.nativeReference 5)]) before 5

theorem before_valid : Valid before := by simp [Valid,before,limit,← ByteArray.size_data]
theorem once_valid : Valid once := by simp [Valid,once,limit,← ByteArray.size_data]
theorem twice_valid : Valid twice := by simp [Valid,twice,limit,← ByteArray.size_data]
theorem before_ready : blocked before = false := rfl
theorem once_ready : blocked once = false := rfl
theorem first_step : syncStep before = some (.Ok (),once) := by simp [syncStep,before,once,syncChoice,action]
theorem second_step : syncStep once = some (.Ok (),twice) := by simp [syncStep,once,twice,syncChoice,action]


/-- Actual release and synchronization calls share the file and persist its visible byte. -/
theorem release_sync_protocol (env : Environment) (counter : Nat) (bounded : 5 ≤ counter)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let _ ← Rustler.executeNative
        (__RELEASE__ owner)
        (fun _ => .tuple #[])
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let _ ← Rustler.executeNative
        (__SYNC__ owner) Rustler.encodeBool
      let owner ← NativeResourceArc.decode (.nativeReference 5)
      let result ← Rustler.executeNative
        (__SYNC__ owner) Rustler.encodeBool
      Result.ok result) (pinnedEnv env before counter) =
      (.ok Term.true,pinnedEnv env twice (counter + 3)) ∧
    lookup ⟨1⟩ (pinnedEnv env twice (counter + 3)) = some twice ∧
    twice.durable = ⟨#[2]⟩ := by
  constructor
  · simp only [release_next env before counter bounded _ registered]
    simp only [sync_next env before once (counter + 1) (by omega) before_valid before_ready first_step _ registered]
    simp only [sync_next env once twice (counter + 1 + 1) (by omega) once_valid once_ready second_step _ registered]
    simp [Nat.add_assoc]
  · constructor
    · simp [lookup,pinnedEnv,NativeResourceArc.vmCells,fileCell,decode_valid twice twice_valid]
    · rfl

end FileResource.Calls
