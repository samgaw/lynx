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
    Result.handle_nativeGet, Result.handle_nativeSet, Result.nativeGet_bind, Result.nativeSet_bind,
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
      rw [show decodedEnv env value (counter+1) = ownedEnv env value ((counter+1)+1) ((counter+1)+1) from rfl,
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
    rw [show decodedEnv env value (counter+1) = ownedEnv env value ((counter+1)+1) ((counter+1)+1) from rfl,
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
  rw [read_native_handled_next env value counter bounded]
  rw [release_handled_next env value (counter+1) (counter+2) (by omega)]
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
  rw [release_handled_next env updated (counter+1) (counter+2) (by omega)]
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
  rw [decode_handled_next env value counter bounded _ handler next registered]
  rw [show decodedEnv env value counter = ownedEnv env value (counter+1) (counter+1) from rfl,
    release_handled_next env value (counter+1) (counter+1) (by omega)]
  simp [Result.handle]

end Shared.Properties
