module
public import Shared.Critical
public import Shared.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Shared.Properties

@[expose] def cell (value : U64) : Nat × String × Term :=
  (1, NativeMutex.typeName effects_core.Counter,
    .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode ({value} : effects_core.Counter)])

@[expose] def payload : CounterResource := ⟨⟨1⟩⟩

@[expose] def pinnedEnv (env : Environment) (value : U64) (counter : Nat := 5) : Environment :=
  { env with
    nativeRefCounter := counter
    nativeHeap := NativeResourceArc.vmCells payload 2 4 5 ++ [cell value]}

@[expose] def ownedEnv (env : Environment) (value : U64) (token counter : Nat) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := [
    (token, NativeResourceArc.handleType CounterResource, .nativeReference 2),
    (5, NativeResourceArc.termType CounterResource, .tuple #[.nativeReference 2, .nativeReference 4]),
    (4, NativeResourceArc.handleType CounterResource, .nativeReference 2),
    (2, NativeResourceArc.typeName CounterResource, .tuple #[.integer 2, NativeCodec.encode payload]), cell value]}

@[expose] def decodedEnv (env : Environment) (value : U64) (counter : Nat) : Environment :=
  ownedEnv env value (counter + 1) (counter + 1)

theorem pin (env : Environment) (value : U64) (counter : Nat) (bounded : 5 ≤ counter) :
    NativeResourceArc.Pinned payload 2 4 5 (pinnedEnv env value counter) := by
  constructor
  · simpa [pinnedEnv] using bounded
  · intro c member
    simp only [pinnedEnv, NativeResourceArc.vmCells, List.cons_append, List.nil_append,
      List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [pinnedEnv, cell] <;> omega
  · simp [pinnedEnv, NativeResourceArc.vmCells, cell, List.filter]
  · simp [pinnedEnv, NativeResourceArc.vmCells, cell, List.filter]
  · simp [pinnedEnv, NativeResourceArc.vmCells, cell, List.filter]
  · simp [pinnedEnv, NativeResourceArc.vmCells, cell, List.filter, NativeMutex.typeName,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType]

theorem decode_next {α : Type} (env : Environment) (value : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : NativeResourceArc CounterResource → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    (NativeResourceArc.decode (.nativeReference 5) >>= next) (pinnedEnv env value counter) =
      next ⟨2, counter + 1⟩ (decodedEnv env value counter) := by
  have decoded := NativeResourceArc.decode_pinned_next payload next (pinnedEnv env value counter)
    2 4 5 (pin env value counter bounded) registered
  simpa [pinnedEnv, decodedEnv, ownedEnv, NativeResourceArc.vmCells, cell, List.map] using decoded

theorem create_next {α : Type} (value : U64) (env : Environment) (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) (zero : env.nativeRefCounter = 0) :
    (Rustler.executeNative (do
      let owner ← __CREATE__ value
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      Result.ok term) id >>= next) env =
      next (.nativeReference 5) (pinnedEnv env value) := by
  let allocated : Environment := {env with nativeRefCounter := 1, nativeHeap := [cell value]}
  have frame : NativeResourceArc.FrameBelow CounterResource 1 [cell value] := by
    intro c member
    simp only [List.mem_singleton] at member
    subst c
    simp [cell, NativeMutex.typeName, NativeResourceArc.typeName,
      NativeResourceArc.handleType, NativeResourceArc.termType]
  have model := NativeResourceArc.newOwned_encode_release_framed_next payload
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted) next allocated registered frame
  convert model using 1 <;> simp [__CREATE__,
    resource_new, Rustler.executeNative, NativeMutex.new, NativeM.allocate,
    NativeOwnedDrop.drop, empty, zero, allocated, pinnedEnv, cell, payload, bind_assoc,
    Result.handle, Result.handle_nativeGet, Result.handle_nativeSet, Result.nativeGet_bind, Result.nativeSet_bind,
    Result.nativeGet_continuation_apply, Result.nativeSet_continuation_apply]
  all_goals rfl

private theorem fresh_beq (token : Nat) (bounded : 5 < token) (small : Nat) (bound : small ≤ 5) :
    (token == small) = false := by simp; omega

private theorem decoded_fresh (env : Environment) (value : U64) (counter : Nat) (bounded : 5 ≤ counter) :
    (decodedEnv env value counter).nativeHeap.any
      (fun cell => cell.1 == (decodedEnv env value counter).nativeRefCounter + 1) = false := by
  apply List.any_eq_false.mpr
  intro c member
  simp only [decodedEnv, ownedEnv, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    simp only [cell, beq_iff_eq, Bool.eq_false_iff] <;> simp [decodedEnv, ownedEnv] <;> omega

theorem decode_handled_next {α β : Type} (env : Environment) (value : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (finish : NativeResourceArc CounterResource → NativeM α)
    (handler : Exception → NativeM α) (next : α → NativeM β)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    ((Result.handle (NativeResourceArc.decode (.nativeReference 5) >>= finish) handler) >>= next) (pinnedEnv env value counter) =
      ((Result.handle (finish ⟨2, counter + 1⟩) handler) >>= next) (decodedEnv env value counter) := by
  have decoded := NativeResourceArc.decode_pinned_handled_next payload finish handler next (pinnedEnv env value counter)
    2 4 5 (pin env value counter bounded) registered
  simpa [pinnedEnv, decodedEnv, ownedEnv, NativeResourceArc.vmCells, cell, List.map] using decoded


theorem release_handled_next {α β : Type} (env : Environment) (value : U64) (token counter : Nat)
    (bounded : 5 < token) (finish : NativeM α) (handler : Exception → NativeM α) (next : α → NativeM β) :
    ((Result.handle (do resource_release ⟨2,token⟩; finish) handler) >>= next) (ownedEnv env value token counter) =
      ((Result.handle finish handler) >>= next) (pinnedEnv env value counter) := by
  have h1 := fresh_beq token bounded 1 (by decide)
  have h2 := fresh_beq token bounded 2 (by decide)
  have h4 := fresh_beq token bounded 4 (by decide)
  have h5 := fresh_beq token bounded 5 (by decide)
  have r1 := BEq.symm_false h1
  have r2 := BEq.symm_false h2
  have r4 := BEq.symm_false h4
  have r5 := BEq.symm_false h5
  have released := NativeResourceArc.releaseOwned_retained_handled_next
    (⟨2,token⟩ : NativeResourceArc CounterResource) payload finish handler next (ownedEnv env value token counter)
    (by simp [List.filter, ownedEnv, cell, r1, r2, r4, r5])
    (by simp [List.filter, ownedEnv, cell, h2])
    (by simp [List.filter, ownedEnv, cell, NativeMutex.typeName,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType])
  simpa [resource_release, NativeOwnedDrop.drop, List.filter, List.map, bne_eq,
    ownedEnv, pinnedEnv, NativeResourceArc.vmCells, cell, h1, h2, h4, h5, r1, r2, r4, r5] using released


theorem deref_handled_next {α β : Type} (env : Environment) (value : U64) (token counter : Nat)
    (bounded : 5 < token) (finish : CounterResource → NativeM α) (handler : Exception → NativeM α) (next : α → NativeM β) :
    ((Result.handle (NativeResourceArc.deref (⟨2,token⟩ : NativeResourceArc CounterResource) >>= finish) handler) >>= next)
      (ownedEnv env value token counter) = ((Result.handle (finish payload) handler) >>= next) (ownedEnv env value token counter) := by
  have r1 := BEq.symm_false (fresh_beq token bounded 1 (by decide))
  have r2 := BEq.symm_false (fresh_beq token bounded 2 (by decide))
  have r4 := BEq.symm_false (fresh_beq token bounded 4 (by decide))
  have r5 := BEq.symm_false (fresh_beq token bounded 5 (by decide))
  have h2 := fresh_beq token bounded 2 (by decide)
  apply NativeResourceArc.deref_retained_handled_next (value := payload)
  · simp [List.filter, ownedEnv, cell, r1, r2, r4, r5]
  · simp [List.filter, ownedEnv, cell, h2]
  · simp [List.filter, ownedEnv, cell, NativeMutex.typeName,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType]


theorem update_native_handled_next {α β : Type} (env : Environment) (value amount : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (finish : Bool → NativeM α) (handler : Exception → NativeM α) (next : α → NativeM β) :
    ∃ changed updated,
      ((Result.handle (resource_locked_increment ⟨2,counter+1⟩ amount >>= finish) handler) >>= next) (decodedEnv env value counter) =
        ((Result.handle (finish changed) handler) >>= next) (ownedEnv env updated (counter+1) (counter+2)) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  cases counter with
  | zero => omega
  | succ counter =>
    have h1 := fresh_beq ((counter+1)+1) (by omega) 1 (by decide)
    obtain ⟨changed, updated, computed, arithmetic⟩ := Shared.Critical.critical_state_handled_next
      finish handler next (⟨1⟩ : NativeMutex effects_core.Counter) ⟨value⟩ amount false (decodedEnv env value (counter+1))
      (by simp [decodedEnv, ownedEnv, cell, List.filter, h1]) (decoded_fresh env value (counter+1) bounded)
    refine ⟨changed, updated.value, ?_, ?_⟩
    · simp only [resource_locked_increment, monadLift_self, bind_assoc]
      simp only [show decodedEnv env value (counter+1) = ownedEnv env value ((counter+1)+1) ((counter+1)+1) from rfl,
        deref_handled_next env value ((counter+1)+1) ((counter+1)+1) (by omega)]
      cases updated
      simpa [decodedEnv, ownedEnv, cell, payload, List.map, h1, (by omega : (counter+1) ≠ 0), Nat.add_assoc] using computed
    · cases changed <;> cases updated <;> simpa using arithmetic


theorem read_native_handled_next {α β : Type} (env : Environment) (value : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (finish : U64 → NativeM α) (handler : Exception → NativeM α) (next : α → NativeM β) :
    ((Result.handle (resource_locked_value ⟨2,counter+1⟩ >>= finish) handler) >>= next) (decodedEnv env value counter) =
      ((Result.handle (finish value) handler) >>= next) (ownedEnv env value (counter+1) (counter+2)) := by
  cases counter with
  | zero => omega
  | succ counter =>
    have h1 := fresh_beq ((counter+1)+1) (by omega) 1 (by decide)
    have read := Shared.Critical.locked_read_handled_next finish handler next (⟨1⟩ : NativeMutex effects_core.Counter)
      ⟨value⟩ (decodedEnv env value (counter+1))
      (by simp [decodedEnv, ownedEnv, cell, List.filter, h1]) (decoded_fresh env value (counter+1) bounded)
    simp only [resource_locked_value, monadLift_self, bind_assoc]
    simp only [show decodedEnv env value (counter+1) = ownedEnv env value ((counter+1)+1) ((counter+1)+1) from rfl,
      deref_handled_next env value ((counter+1)+1) ((counter+1)+1) (by omega)]
    simpa [payload, NativeM.ok, decodedEnv, ownedEnv, cell, List.map, h1, (by omega : (counter+1) ≠ 0), Nat.add_assoc] using read


theorem read_call_next {α : Type} (env : Environment) (value : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative
        (__READ__ owner) Rustler.encodeUnsigned
      next result) (pinnedEnv env value counter) =
      next (.integer value.val) (pinnedEnv env value (counter+2)) := by
  rw [decode_next env value counter bounded _ registered]
  simp only [Rustler.executeNative, __READ__,
    monadLift_self, bind_assoc, NativeM.ok, Result.ok_bind]
  simp only [read_native_handled_next env value counter bounded]
  simp only [release_handled_next env value (counter+1) (counter+2) (by omega)]
  simp [Result.handle, Rustler.encodeUnsigned]

theorem add_call_next {α : Type} (env : Environment) (value amount : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    ∃ changed updated,
      (do
        let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
        let result ← Rustler.executeNative
          (__ADD__ owner amount) Rustler.encodeBool
        next result) (pinnedEnv env value counter) =
        next (Rustler.encodeBool changed) (pinnedEnv env updated (counter+2)) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  let finish : Bool → NativeM Term := fun changed => do
    resource_release ⟨2,counter+1⟩
    Result.ok (Rustler.encodeBool changed)
  let handler : Exception → NativeM Term := fun error => match error with
    | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
    | _ => Result.error .exhausted
  obtain ⟨changed, updated, computed, arithmetic⟩ :=
    update_native_handled_next env value amount counter bounded finish handler next
  refine ⟨changed, updated, ?_, arithmetic⟩
  rw [decode_next env value counter bounded _ registered]
  simp only [Rustler.executeNative, __ADD__,
    monadLift_self, bind_assoc, NativeM.ok, Result.ok_bind]
  change ((Result.handle (resource_locked_increment ⟨2,counter+1⟩ amount >>= finish) handler) >>= next) _ = _
  rw [computed]
  simp only [finish]
  simp only [release_handled_next env updated (counter+1) (counter+2) (by omega)]
  simp [Result.handle]

theorem add_safe_call_next {α : Type} (env : Environment) (value amount total : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (fits : value.val + amount.val ≤ U64.max) (sum : total.val = value.val + amount.val) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative
        (__ADD__ owner amount) Rustler.encodeBool
      next result) (pinnedEnv env value counter) =
      next (.atom "true") (pinnedEnv env total (counter+2)) := by
  obtain ⟨changed, updated, computed, arithmetic⟩ := add_call_next env value amount counter bounded next registered
  cases changed
  · simp only [Bool.false_eq_true, ↓reduceIte] at arithmetic
    omega
  · simp only [↓reduceIte] at arithmetic
    have same : updated = total := UScalar.eq_of_val_eq (by omega)
    subst updated
    exact computed

theorem add_overflow_call_next {α : Type} (env : Environment) (value amount : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (overflow : U64.max < value.val + amount.val) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative
        (__ADD__ owner amount) Rustler.encodeBool
      next result) (pinnedEnv env value counter) =
      next (.atom "false") (pinnedEnv env value (counter+2)) := by
  obtain ⟨changed, updated, computed, arithmetic⟩ := add_call_next env value amount counter bounded next registered
  cases changed
  · simp only [Bool.false_eq_true, ↓reduceIte] at arithmetic
    rw [arithmetic.1] at computed
    exact computed
  · simp only [↓reduceIte] at arithmetic
    have maximum := updated.hmax
    have maximum' : updated.val ≤ U64.max := by scalar_tac
    omega

theorem read_call_at {α : Type} (env : Environment) (value : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [cell value])
    (count : env.nativeRefCounter = counter)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative
        (__READ__ owner) Rustler.encodeUnsigned
      next result) env =
      next (.integer value.val) (pinnedEnv env value (counter+2)) := by
  have same : pinnedEnv env value counter = env := by
    cases env
    simp_all [pinnedEnv]
  have model := read_call_next env value counter bounded next registered
  simpa only [same] using model


theorem add_safe_call_at {α : Type} (env : Environment) (value amount total : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [cell value])
    (count : env.nativeRefCounter = counter)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (fits : value.val + amount.val ≤ U64.max) (sum : total.val = value.val + amount.val) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative
        (__ADD__ owner amount) Rustler.encodeBool
      next result) env =
      next (.atom "true") (pinnedEnv env total (counter+2)) := by
  have same : pinnedEnv env value counter = env := by
    cases env
    simp_all [pinnedEnv]
  have model := add_safe_call_next env value amount total counter bounded next registered fits sum
  simpa only [same] using model


theorem add_overflow_call_at {α : Type} (env : Environment) (value amount : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (next : Term → NativeM α)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [cell value])
    (count : env.nativeRefCounter = counter)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes)
    (overflow : U64.max < value.val + amount.val) :
    (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      let result ← Rustler.executeNative
        (__ADD__ owner amount) Rustler.encodeBool
      next result) env =
      next (.atom "false") (pinnedEnv env value (counter+2)) := by
  have same : pinnedEnv env value counter = env := by
    cases env
    simp_all [pinnedEnv]
  have model := add_overflow_call_next env value amount counter bounded next registered overflow
  simpa only [same] using model

theorem payload_cleanup (value : CounterResource) :
    CounterResource.drop_owned value = NativeMutex.dispose value.state := rfl

theorem decoder_badarg_cleanup_at {α β : Type} (env : Environment) (value : U64) (counter : Nat)
    (bounded : 5 ≤ counter) (handler : Exception → NativeM α) (next : α → NativeM β)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 2 4 5 ++ [cell value])
    (count : env.nativeRefCounter = counter)
    (registered : NativeResourceArc.typeName CounterResource ∈ env.nativeResourceTypes) :
    ((Result.handle (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      NativeOwnedDrop.drop owner
      Result.error (.error (.atom "badarg"))) handler) >>= next) env =
      (handler (.error (.atom "badarg")) >>= next) (pinnedEnv env value (counter+1)) := by
  have cleanup (owner : NativeResourceArc CounterResource) :
      NativeOwnedDrop.drop owner = resource_release owner := by simp [resource_release]
  have same : env = pinnedEnv env value counter := by cases env; simp_all [pinnedEnv]
  conv_lhs => rw [same]
  simp only [cleanup]
  simp only [decode_handled_next env value counter bounded _ handler next registered]
  simp only [show decodedEnv env value counter = ownedEnv env value (counter+1) (counter+1) from rfl,
    release_handled_next env value (counter+1) (counter+1) (by omega)]
  simp [Result.handle]

/-- The actual cross-crate Rust borrow/update accepts arbitrary unrelated heap
cells and any validated owner count. Only the mutex cell changes; overflow
preserves its value, and poisoned acquisition preserves the poison status. -/
theorem update_framed_prefix
    (resource : NativeResourceArc CounterResource) (mutex : NativeMutex effects_core.Counter)
    (value amount : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (positive : 0 < count) (bounded : count ≤ NativeResourceArc.referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == resource.token) =
      [(resource.token,NativeResourceArc.handleType CounterResource,.nativeReference resource.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == resource.id) =
      [(resource.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference resource.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    ∃ changed updated,
      Result.ReadyPrefix (resource_locked_increment resource amount) env (.ok changed) {env with
        nativeRefCounter := env.nativeRefCounter + 1,
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
            .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value := updated} : effects_core.Counter)])
          else cell} ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed,updated,computed,arithmetic⟩ := Shared.Critical.critical_prefix
    mutex ({value} : effects_core.Counter) amount poisoned env stored fresh
  have head := (NativeResourceArc.deref_live_prefix resource ({state := mutex} : CounterResource)
    count env positive bounded token allocation owners).bind
      (fun payload => effects_core.locked_increment payload.state amount)
  simp only [Result.ok_bind] at head
  rcases updated with ⟨updated⟩
  refine ⟨changed,updated,?_,?_⟩
  · simpa only [resource_locked_increment,monadLift_self] using head.trans computed
  · cases changed <;> simpa using arithmetic

theorem update_framed_handled_next {α β : Type}
    (resource : NativeResourceArc CounterResource) (mutex : NativeMutex effects_core.Counter)
    (value amount : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (finish : Bool → NativeM α) (handler : Exception → NativeM α) (next : α → NativeM β)
    (positive : 0 < count) (bounded : count ≤ NativeResourceArc.referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == resource.token) =
      [(resource.token,NativeResourceArc.handleType CounterResource,.nativeReference resource.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == resource.id) =
      [(resource.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference resource.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    ∃ changed updated,
      ((Result.handle (resource_locked_increment resource amount >>= finish) handler) >>= next) env =
      ((Result.handle (finish changed) handler) >>= next) {env with
        nativeRefCounter := env.nativeRefCounter + 1,
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
            .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value := updated} : effects_core.Counter)])
          else cell} ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed,updated,trace,arithmetic⟩ := update_framed_prefix resource mutex value amount count
    poisoned env positive bounded token allocation owners stored fresh
  refine ⟨changed,updated,?_,arithmetic⟩
  simpa only [Result.ok_bind] using (((trace.bind finish).handle handler).bind next).apply

/-- Reading through the actual resource and cross-crate guard leaves unrelated
heap cells in place, independently of the number of other validated owners. -/
theorem read_framed_prefix
    (resource : NativeResourceArc CounterResource) (mutex : NativeMutex effects_core.Counter)
    (value : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (positive : 0 < count) (bounded : count ≤ NativeResourceArc.referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == resource.token) =
      [(resource.token,NativeResourceArc.handleType CounterResource,.nativeReference resource.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == resource.id) =
      [(resource.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference resource.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    Result.ReadyPrefix (resource_locked_value resource) env (.ok value) {env with
      nativeRefCounter := env.nativeRefCounter + 1
      nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
        (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)]) else cell} := by
  have head := (NativeResourceArc.deref_live_prefix resource ({state := mutex} : CounterResource)
    count env positive bounded token allocation owners).bind (fun payload => do
      let acquired ← NativeMutex.lock payload.state
      let guard ← effects_core.recover_guard acquired
      let observed ← effects_core.read_guard guard
      effects_core.release_guard guard
      Result.ok observed)
  simp only [Result.ok_bind] at head
  have read := Shared.Critical.locked_read_prefix mutex ({value} : effects_core.Counter) poisoned env stored fresh
  simpa only [resource_locked_value,monadLift_self,NativeM.ok] using head.trans read

theorem read_framed_handled_next {α β : Type}
    (resource : NativeResourceArc CounterResource) (mutex : NativeMutex effects_core.Counter)
    (value : U64) (count : Nat) (env : Environment)
    (finish : U64 → NativeM α) (handler : Exception → NativeM α) (next : α → NativeM β)
    (positive : 0 < count) (bounded : count ≤ NativeResourceArc.referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == resource.token) =
      [(resource.token,NativeResourceArc.handleType CounterResource,.nativeReference resource.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == resource.id) =
      [(resource.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference resource.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom "unpoisoned",NativeCodec.encode ({value} : effects_core.Counter)])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    ((Result.handle (resource_locked_value resource >>= finish) handler) >>= next) env =
      ((Result.handle (finish value) handler) >>= next) {env with
        nativeRefCounter := env.nativeRefCounter + 1,
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
            .atom "unpoisoned",NativeCodec.encode ({value} : effects_core.Counter)]) else cell} := by
  have trace := read_framed_prefix resource mutex value count false env positive bounded token allocation owners stored fresh
  simpa only [Result.ok_bind,Bool.false_eq_true,↓reduceIte] using (((trace.bind finish).handle handler).bind next).apply

namespace Framed

@[expose] def counterCell (id : Nat) (value : U64) : Nat × String × Term :=
  (id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",.atom "unpoisoned",
    NativeCodec.encode ({value} : effects_core.Counter)])

/-- Two independent VM-pinned resources share an otherwise ordinary runtime.
The two mutexes and their ownership/registry cells have distinct identities. -/
@[expose] def heap (value other : U64) : List (Nat × String × Term) :=
  NativeResourceArc.vmCells ({state := ⟨1⟩} : CounterResource) 2 4 5 ++
  [counterCell 1 value] ++
  NativeResourceArc.vmCells ({state := ⟨11⟩} : CounterResource) 12 14 15 ++
  [counterCell 11 other,(17,"unrelated",.tuple #[.integer 99])]

@[expose] def initialFor (value : U64) : Environment :=
  {nativeRefCounter := 42, nativeHeap := heap value 11#u64,
    nativeResourceTypes := [NativeResourceArc.typeName CounterResource],
    pdict := [(.atom "counter",.nativeReference 5),(.atom "other",.nativeReference 15)]}
@[expose] def initial : Environment := initialFor 7#u64
@[expose] def overflowInitial : Environment := initialFor 18446744073709551615#u64

/-- Two Rust owners and a VM pin of the first resource coexist with an entirely
separate resource and its mutex. No decoder count of two is assumed. -/
@[expose] def coowned (value : U64) (counter : Nat) : Environment :=
  {nativeRefCounter := counter,nativeHeap :=
    [(3,NativeResourceArc.handleType CounterResource,.nativeReference 2),
     (6,NativeResourceArc.handleType CounterResource,.nativeReference 2),
     (4,NativeResourceArc.handleType CounterResource,.nativeReference 2),
     (5,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference 2,.nativeReference 4]),
     (2,NativeResourceArc.typeName CounterResource,
       .tuple #[.integer 3,NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]),counterCell 1 value] ++
    NativeResourceArc.vmCells ({state := ⟨11⟩} : CounterResource) 12 14 15 ++
    [counterCell 11 11#u64,(17,"unrelated",.tuple #[.integer 99])]}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
/-- Actual cross-crate Rust mutation preserves all three owners and every
foreign cell while changing only the first mutex payload and fresh counter. -/
theorem coowned_update :
    Rustler.executeNative (resource_locked_increment ⟨2,3⟩ 3#u64) Rustler.encodeBool
      (coowned 7#u64 42) = (.ok Term.true,coowned 10#u64 43) := by
  let finish : Bool → NativeM Term := fun changed => Result.ok (Rustler.encodeBool changed)
  let handler : Exception → NativeM Term := fun error => match error with
    | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
    | _ => Result.error .exhausted
  have execute (body : NativeM Bool) :
      Rustler.executeNative body Rustler.encodeBool = Result.handle (body >>= finish) handler := by
    simp only [Rustler.executeNative,finish]
    congr 1
  obtain ⟨changed,updated,computed,arithmetic⟩ := update_framed_handled_next
    (⟨2,3⟩ : NativeResourceArc CounterResource) (⟨1⟩ : NativeMutex effects_core.Counter)
    7#u64 3#u64 3 false (coowned 7#u64 42) finish handler Result.ok (by decide) (by decide)
    (by simp [coowned,counterCell,NativeResourceArc.vmCells])
    (by simp [coowned,counterCell,NativeResourceArc.vmCells])
    (by simp [coowned,counterCell,NativeResourceArc.vmCells,NativeMutex.typeName,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType])
    (by simp [coowned,counterCell,NativeResourceArc.vmCells])
    (by simp [coowned,counterCell,NativeResourceArc.vmCells])
  cases changed with
  | false =>
      have overflow : U64.max < (7#u64).val + (3#u64).val := arithmetic.2
      have fits : (7#u64).val + (3#u64).val ≤ U64.max := by scalar_tac
      exact False.elim ((Nat.not_lt_of_ge fits) overflow)
  | true =>
      have equal : updated = 10#u64 := UScalar.eq_of_val_eq (by simpa using arithmetic)
      subst updated
      simp only [finish,handler,Result.bind_ok,Result.handle,Result.ok_apply,Rustler.encodeBool] at computed
      change _ = (Outcome.ok Term.true,coowned 10#u64 43) at computed
      rw [execute]
      exact computed

@[expose] def accepted (value : U64) (config : Concurrent.Config Term) : Bool :=
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  config.outcome.isTrue && env.nativeRefCounter == 48 &&
    (heap value 11#u64).all env.nativeHeap.contains &&
    env.nativeHeap.length == (heap value 11#u64).length &&
    env.nativeResourceTypes.contains (NativeResourceArc.typeName CounterResource)

theorem accepted_outcome (value : U64) (config : Concurrent.Config Term)
    (checked : accepted value config = true) : config.outcome = .ok Term.true := by
  apply Outcome.eq_of_isTrue
  simp only [accepted,Bool.and_eq_true] at checked
  exact checked.1.1.1.1

end Framed

end Shared.Properties
