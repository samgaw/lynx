module
public import Shared.Properties
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Shared.FramedCalls

private abbrev Cell := Nat × String × Term
private def replace (id : Nat) (tag : String) (contents : Term) (cell : Cell) : Cell :=
  if cell.1 == id then (id,tag,contents) else cell

private theorem replace_key (id : Nat) (tag : String) (contents : Term) (cell : Cell) :
    (replace id tag contents cell).1 = cell.1 := by
  unfold replace
  split
  · rename_i same
    exact (show cell.1 = id from by simpa using same).symm
  · rfl

private theorem filter_replace (heap : List Cell) (id key : Nat) (tag : String) (contents : Term) :
    (heap.map (replace id tag contents)).filter (fun cell => cell.1 == key) =
      (heap.filter (fun cell => cell.1 == key)).map (replace id tag contents) := by
  simp only [List.filter_map,Function.comp_def,replace_key]

private theorem known_cell (heap : List Cell) (id : Nat) (tag : String) (contents : Term)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id,tag,contents)])
    (cell : Cell) (member : cell ∈ heap) (same : cell.1 = id) : cell = (id,tag,contents) := by
  have included : cell ∈ heap.filter (fun cell => cell.1 == id) :=
    List.mem_filter.mpr ⟨member,by simp [same]⟩
  simpa [stored] using included

private theorem replace_owners (heap : List Cell) (id resource : Nat)
    (tag : String) (before after : Array Term)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id,tag,.tuple before)]) :
    ((heap.map (replace id tag (.tuple after))).filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference resource)).length =
    (heap.filter (fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference resource)).length := by
  rw [List.filter_map,List.length_map]
  congr 1
  apply List.filter_congr
  intro cell member
  by_cases same : cell.1 = id
  · have equal := known_cell heap id tag (.tuple before) stored cell member same
    subst cell
    have separate (fields : Array Term) : ((Term.tuple fields) == Term.nativeReference resource) = false := by
      apply Bool.eq_false_iff.mpr
      simp [Term.nativeReference]
    simp [replace,separate]
  · simp [replace,same]

private theorem key_bounded (heap : List Cell) (limit id : Nat) (tag : String) (contents : Term)
    (keys : ∀ cell ∈ heap, cell.1 ≤ limit)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id,tag,contents)]) : id ≤ limit := by
  have member : (id,tag,contents) ∈ heap.filter (fun cell => cell.1 == id) := by simp [stored]
  exact keys _ (List.mem_filter.mp member).1

private theorem fresh_key (heap : List Cell) (limit id : Nat)
    (keys : ∀ cell ∈ heap, cell.1 ≤ limit) (fresh : limit < id) :
    heap.any (fun cell => cell.1 == id) = false := by
  simp only [List.any_eq_false]
  intro cell member
  have := keys cell member
  simp only [beq_iff_eq]
  omega

private theorem replace_restore (heap : List Cell) (id : Nat) (tag : String) (before after : Term)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id,tag,before)]) :
    (heap.map (replace id tag after)).map (replace id tag before) = heap := by
  rw [List.map_map]
  calc
    _ = heap.map (fun cell => cell) := List.map_congr_left (by
      intro cell member
      by_cases same : cell.1 = id
      · have equal := known_cell heap id tag before stored cell member same
        subst cell
        simp [replace]
      · simp [replace,same])
    _ = heap := List.map_id' heap

private theorem replace_commute (heap : List Cell) (left right : Nat)
    (leftTag rightTag : String) (leftValue rightValue : Term) (different : left ≠ right) :
    (heap.map (replace left leftTag leftValue)).map (replace right rightTag rightValue) =
      (heap.map (replace right rightTag rightValue)).map (replace left leftTag leftValue) := by
  simp only [List.map_map]
  congr 1
  funext cell
  by_cases l : cell.1 = left <;> by_cases r : cell.1 = right <;>
    simp_all [replace]

private theorem erase_replace (heap : List Cell) (id key : Nat) (tag : String) (contents : Term) :
    (heap.map (replace id tag contents)).filter (fun cell => cell.1 != key) =
      (heap.filter (fun cell => cell.1 != key)).map (replace id tag contents) := by
  simp only [List.filter_map,Function.comp_def,replace_key]

private theorem erase_fresh (heap : List Cell) (limit id : Nat)
    (keys : ∀ cell ∈ heap, cell.1 ≤ limit) (fresh : limit < id) :
    heap.filter (fun cell => cell.1 != id) = heap := by
  apply List.filter_eq_self.mpr
  intro cell member
  have := keys cell member
  simp only [bne_iff_ne]
  omega

private theorem filter_fresh (heap : List Cell) (limit id : Nat)
    (keys : ∀ cell ∈ heap, cell.1 ≤ limit) (fresh : limit < id) :
    heap.filter (fun cell => cell.1 == id) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  have := keys cell member
  simp only [beq_iff_eq]
  omega

/-- The actual Rustler computation decodes one fresh owner, runs the extracted
cross-crate mutation and consumes that owner. Other owners and heap cells remain
in place. Registration, live-owner bounds and keyed heap views are explicit
preconditions. -/
theorem add_call_prefix
    (pin : NativeResourceArc CounterResource) (term : Nat) (mutex : NativeMutex effects_core.Counter)
    (value amount : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (different : pin.id ≠ mutex.id) :
    ∃ changed updated,
      Result.ReadyPrefix (do
        let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
        Rustler.executeNative (__ADD__ owner amount) Rustler.encodeBool) env
        (.ok (Rustler.encodeBool changed)) {env with
          nativeRefCounter := env.nativeRefCounter + 2,
          nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
            (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
              .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value := updated} : effects_core.Counter)])
            else cell} ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  let payload : CounterResource := {state := mutex}
  let owner : NativeResourceArc CounterResource := ⟨pin.id,env.nativeRefCounter + 1⟩
  let decoded : Environment := {env with
    nativeRefCounter := env.nativeRefCounter + 1
    nativeHeap := (env.nativeRefCounter + 1,NativeResourceArc.handleType CounterResource,.nativeReference pin.id) ::
      env.nativeHeap.map (replace pin.id (NativeResourceArc.typeName CounterResource)
        (.tuple #[.integer (count + 1),NativeCodec.encode payload]))}
  have resourceBound := key_bounded env.nativeHeap env.nativeRefCounter pin.id _ _ keys allocation
  have mutexBound := key_bounded env.nativeHeap env.nativeRefCounter mutex.id _ _ keys stored
  have resourceFresh : env.nativeRefCounter + 1 ≠ pin.id := by omega
  have mutexFresh : env.nativeRefCounter + 1 ≠ mutex.id := by omega
  have absent := filter_fresh env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have fresh := fresh_key env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have newToken : decoded.nativeHeap.filter (fun cell => cell.1 == owner.token) =
      [(owner.token,NativeResourceArc.handleType CounterResource,.nativeReference owner.id)] := by
    simp [decoded,owner,filter_replace,absent]
  have newAllocation : decoded.nativeHeap.filter (fun cell => cell.1 == owner.id) =
      [(owner.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer (count + 1),NativeCodec.encode payload])] := by
    simp [decoded,owner,filter_replace,allocation,replace,resourceFresh]
  have newOwners : (decoded.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference owner.id).length = count + 1 := by
    simp [decoded,owner,replace_owners env.nativeHeap pin.id pin.id _ _ _ allocation,owners]
  have newStored : decoded.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])] := by
    simp [decoded,filter_replace,stored,replace,Ne.symm different,mutexFresh]
  have leaseFresh : decoded.nativeHeap.any (fun cell => cell.1 == decoded.nativeRefCounter + 1) = false := by
    simp only [decoded,List.any_cons,List.any_map,Function.comp_def,replace_key]
    simp [fresh_key env.nativeHeap env.nativeRefCounter ((env.nativeRefCounter + 1) + 1) keys (by omega)]
  obtain ⟨changed,updated,computed,arithmetic⟩ := Shared.Properties.update_framed_prefix
    owner mutex value amount (count + 1) poisoned decoded
    (by omega) (by omega) newToken newAllocation newOwners newStored leaseFresh
  let after : Environment := {decoded with
    nativeRefCounter := decoded.nativeRefCounter + 1
    nativeHeap := decoded.nativeHeap.map (replace mutex.id (NativeMutex.typeName effects_core.Counter)
      (.tuple #[.atom "unlocked",.atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode ({value := updated} : effects_core.Counter)]))}
  have afterToken : after.nativeHeap.filter (fun cell => cell.1 == owner.token) =
      [(owner.token,NativeResourceArc.handleType CounterResource,.nativeReference owner.id)] := by
    simp [after,filter_replace,newToken,replace,owner,mutexFresh]
  have afterAllocation : after.nativeHeap.filter (fun cell => cell.1 == owner.id) =
      [(owner.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer (count + 1),NativeCodec.encode payload])] := by
    simp [after,filter_replace,newAllocation,replace,owner,different]
  have afterOwners : (after.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference owner.id).length = count + 1 := by
    simpa only [after] using (replace_owners decoded.nativeHeap mutex.id owner.id _ _ _ newStored).trans newOwners
  have released := NativeResourceArc.releaseOwned_live_prefix owner payload (count + 1) after
    (by omega) (by omega) afterToken afterAllocation afterOwners
  let final : Environment := {env with
    nativeRefCounter := env.nativeRefCounter + 2
    nativeHeap := env.nativeHeap.map (replace mutex.id (NativeMutex.typeName effects_core.Counter)
      (.tuple #[.atom "unlocked",.atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode ({value := updated} : effects_core.Counter)]))}
  have restored : {after with nativeHeap :=
      (after.nativeHeap.filter fun cell => cell.1 != owner.token).map fun cell =>
        if cell.1 == owner.id then
          (owner.id,NativeResourceArc.typeName CounterResource,
            .tuple #[.integer ((↑(count + 1) : Int) - 1),NativeCodec.encode payload]) else cell} = final := by
    change {after with
      nativeHeap := (after.nativeHeap.filter fun cell => cell.1 != owner.token).map
        (replace owner.id (NativeResourceArc.typeName CounterResource)
          (.tuple #[.integer ((↑(count + 1) : Int) - 1),NativeCodec.encode payload]))} = final
    simp only [after,decoded,owner,List.map_cons]
    have sameOwner : replace mutex.id (NativeMutex.typeName effects_core.Counter)
        (.tuple #[.atom "unlocked",.atom (if poisoned then "poisoned" else "unpoisoned"),
          NativeCodec.encode ({value := updated} : effects_core.Counter)])
        (env.nativeRefCounter + 1,NativeResourceArc.handleType CounterResource,.nativeReference pin.id) =
        (env.nativeRefCounter + 1,NativeResourceArc.handleType CounterResource,.nativeReference pin.id) := by
      simp [replace,mutexFresh]
    simp only [sameOwner,List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    rw [erase_replace,erase_replace,erase_fresh env.nativeHeap env.nativeRefCounter
      (env.nativeRefCounter + 1) keys (by omega)]
    have decrement : ((↑(count + 1) : Int) - 1) = count := by omega
    rw [decrement,replace_commute _ mutex.id pin.id _ _ _ _ (Ne.symm different),
      replace_restore env.nativeHeap pin.id _ _ _ allocation]
  have releaseCall : Result.ReadyPrefix (do resource_release owner; Result.ok changed)
      after (.ok changed) final := by
    simpa only [Result.ok_bind,resource_release,monadLift_self,NativeOwnedDrop.drop,restored] using
      released.bind (fun _ => Result.ok changed)
  have bodyTrace : Result.ReadyPrefix (__ADD__ owner amount) decoded (.ok changed) final := by
    rw [__ADD__]
    simp only [monadLift_self,NativeM.ok]
    have headTrace := computed.bind (fun changed => do resource_release owner; Result.ok changed)
    simp only [Result.ok_bind] at headTrace
    exact headTrace.trans releaseCall
  have executed : Result.ReadyPrefix (Rustler.executeNative (__ADD__ owner amount) Rustler.encodeBool)
      decoded (.ok (Rustler.encodeBool changed)) final := by
    simpa only [Rustler.executeNative_ok] using Rustler.executeNative_readyPrefix bodyTrace Rustler.encodeBool
  refine ⟨changed,updated,?_,arithmetic⟩
  have headTrace := (NativeResourceArc.decode_live_prefix pin term payload count env registered
    positive bounded registry token allocation owners fresh).bind (fun owner =>
      Rustler.executeNative (__ADD__ owner amount) Rustler.encodeBool)
  simp only [Result.ok_bind] at headTrace
  exact headTrace.trans executed

theorem add_call_next {α : Type}
    (pin : NativeResourceArc CounterResource) (term : Nat) (mutex : NativeMutex effects_core.Counter)
    (value amount : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (different : pin.id ≠ mutex.id) :
    ∃ changed updated,
      (do
        let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
        let answer ← Rustler.executeNative (__ADD__ owner amount) Rustler.encodeBool
        next answer) env = next (Rustler.encodeBool changed) {env with
          nativeRefCounter := env.nativeRefCounter + 2,
          nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
            (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
              .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value := updated} : effects_core.Counter)])
            else cell} ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed,updated,trace,arithmetic⟩ := add_call_prefix pin term mutex value amount count poisoned env
    registered positive bounded keys registry token allocation owners stored different
  refine ⟨changed,updated,?_,arithmetic⟩
  simpa only [bind_assoc,Result.ok_bind] using (trace.bind next).apply

/-- A later argument rejection consumes only the decoder's temporary owner.
The original owner count and every unrelated heap cell are restored. Verification
exhaustion remains uncatchable in the residual handler. -/
theorem decoder_cleanup_prefix {α : Type}
    (pin : NativeResourceArc CounterResource) (term : Nat) (payload : CounterResource)
    (count : Nat) (env : Environment) (reason : Exception)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode payload])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count) :
    Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
      resource_release owner
      (Result.error reason : NativeM α)) env (Result.error reason)
      {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  let owner : NativeResourceArc CounterResource := ⟨pin.id,env.nativeRefCounter + 1⟩
  let decoded : Environment := {env with
    nativeRefCounter := env.nativeRefCounter + 1
    nativeHeap := (env.nativeRefCounter + 1,NativeResourceArc.handleType CounterResource,.nativeReference pin.id) ::
      env.nativeHeap.map (replace pin.id (NativeResourceArc.typeName CounterResource)
        (.tuple #[.integer (count + 1),NativeCodec.encode payload]))}
  have resourceBound := key_bounded env.nativeHeap env.nativeRefCounter pin.id _ _ keys allocation
  have resourceFresh : env.nativeRefCounter + 1 ≠ pin.id := by omega
  have absent := filter_fresh env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have fresh := fresh_key env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have newToken : decoded.nativeHeap.filter (fun cell => cell.1 == owner.token) =
      [(owner.token,NativeResourceArc.handleType CounterResource,.nativeReference owner.id)] := by
    simp [decoded,owner,filter_replace,absent]
  have newAllocation : decoded.nativeHeap.filter (fun cell => cell.1 == owner.id) =
      [(owner.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer (count + 1),NativeCodec.encode payload])] := by
    simp [decoded,owner,filter_replace,allocation,replace,resourceFresh]
  have newOwners : (decoded.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference owner.id).length = count + 1 := by
    simp [decoded,owner,replace_owners env.nativeHeap pin.id pin.id _ _ _ allocation,owners]
  have released := NativeResourceArc.releaseOwned_live_prefix owner payload (count + 1) decoded
    (by omega) (by omega) newToken newAllocation newOwners
  have restored : {decoded with nativeHeap :=
      (decoded.nativeHeap.filter fun cell => cell.1 != owner.token).map fun cell =>
        if cell.1 == owner.id then
          (owner.id,NativeResourceArc.typeName CounterResource,
            .tuple #[.integer ((↑(count + 1) : Int) - 1),NativeCodec.encode payload]) else cell} =
        {env with nativeRefCounter := env.nativeRefCounter + 1} := by
    change {decoded with
      nativeHeap := (decoded.nativeHeap.filter fun (cell : Cell) => cell.1 != owner.token).map
        (replace owner.id (NativeResourceArc.typeName CounterResource)
          (.tuple #[.integer ((↑(count + 1) : Int) - 1),NativeCodec.encode payload]))} = _
    simp only [decoded,owner,List.filter_cons,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    rw [erase_replace,erase_fresh env.nativeHeap env.nativeRefCounter
      (env.nativeRefCounter + 1) keys (by omega)]
    have decrement : ((↑(count + 1) : Int) - 1) = count := by omega
    rw [decrement,replace_restore env.nativeHeap pin.id _ _ _ allocation]
  have releaseTrace : Result.ReadyPrefix (do resource_release owner; (Result.error reason : NativeM α))
      decoded (Result.error reason) {env with nativeRefCounter := env.nativeRefCounter + 1} := by
    simpa only [Result.ok_bind,resource_release,monadLift_self,NativeOwnedDrop.drop,restored] using
      released.bind (fun _ => (Result.error reason : NativeM α))
  have headTrace := (NativeResourceArc.decode_live_prefix pin term payload count env registered
    positive bounded registry token allocation owners fresh).bind (fun owner => do
      resource_release owner
      (Result.error reason : NativeM α))
  simp only [Result.ok_bind] at headTrace
  exact headTrace.trans releaseTrace

theorem decoder_cleanup_next {α β : Type}
    (pin : NativeResourceArc CounterResource) (term : Nat) (payload : CounterResource)
    (count : Nat) (env : Environment) (reason : Exception)
    (handler : Exception → NativeM α) (next : α → NativeM β)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode payload])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count) :
    ((Result.handle (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
      resource_release owner
      Result.error reason) handler) >>= next) env =
      ((Result.handle (Result.error reason) handler) >>= next)
        {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  have trace := decoder_cleanup_prefix (α := α) pin term payload count env reason
    registered positive bounded keys registry token allocation owners
  exact ((trace.handle handler).bind next).apply

/-- The internal Rust clone root is verified without exporting it as a NIF. -/
theorem clone_prefix
    (handle : NativeResourceArc CounterResource) (value : CounterResource) (count : Nat) (env : Environment)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, NativeResourceArc.handleType CounterResource, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, NativeResourceArc.typeName CounterResource, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference handle.id).length = count)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    Result.ReadyPrefix (resource_clone handle) env
      (.ok (⟨handle.id, env.nativeRefCounter + 1⟩ : NativeResourceArc CounterResource)) {env with
        nativeRefCounter := env.nativeRefCounter + 1, nativeHeap :=
          (env.nativeRefCounter + 1, NativeResourceArc.handleType CounterResource, .nativeReference handle.id) :: env.nativeHeap.map fun cell =>
            if cell.1 == handle.id then
              (handle.id, NativeResourceArc.typeName CounterResource, .tuple #[.integer (count + 1), NativeCodec.encode value]) else cell} := by
  simpa only [resource_clone,monadLift_self] using
    NativeResourceArc.clone_live_prefix handle value count env positive bounded token stored owners fresh

end Shared.FramedCalls
