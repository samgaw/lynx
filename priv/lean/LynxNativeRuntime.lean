module

public import Aeneas
public import Lynx.Term

/-! Interpretation of extracted native computations in Lynx's resumable runtime.
A native panic is retained as the `rust_panicked` marker. It must be converted by
a native facade before becoming an Elixir-visible exception. Undefined behavior
and divergence are verification exhaustion, never successful native returns.
Mutex construction initializes logical shared cells. Bounded blocking acquisition
uses atomic state waits; borrowed guard views reconstruct payload updates.
Normal release commits reconstructed guard payloads and unlocks owned cells.
Rust-owned resource tokens share heap payload identities; mutex fields retain
shared cells. Explicit loader registration, bounded retain/release and optional
extracted structural cleanup cover supported Rust-owned lifecycles. Resource extraction admission, VM pins,
callbacks, native executors and FFI execution require separate checks/models. -/

public section

open Aeneas Aeneas.Std

namespace Lynx

abbrev NativeM (α : Type) := Result α

namespace NativeM

@[expose] def ok {α : Type} (value : α) : NativeM α := Result.ok value

@[expose] def fail {α : Type} (error : Error) : NativeM α :=
  match error with
  | .panic => .error (.error (.atom "rust_panicked"))
  | .undef => .error .exhausted

@[expose] def lift {α : Type} (value : α) : NativeM α := Result.ok value

@[expose] def massert (condition : Prop) [Decidable condition] : NativeM Unit :=
  if condition then Result.ok () else fail .panic

/-- A bounded interpreter for extracted loop bodies. Continuation state and
all effects survive each iteration; a cutoff is verification exhaustion. -/
@[expose] def loopFuel {α β : Type} (body : α → NativeM (Aeneas.Std.ControlFlow α β)) :
    Nat → α → NativeM β
  | 0, _ => Result.error .exhausted
  | fuel + 1, state => do
    match ← body state with
    | .cont next => loopFuel body fuel next
    | .done value => NativeM.ok value

/-- One iteration per possible four-byte file record plus the terminating test.
This is a verification bound, not a Rust runtime limit or a liveness claim. -/
@[expose] def loop {α β : Type} (body : α → NativeM (Aeneas.Std.ControlFlow α β)) (state : α) : NativeM β :=
  loopFuel body 262145 state

/-- Lift a standard Aeneas primitive without replacing its implementation. -/
@[expose] def fromRust {α : Type} (computation : RustM α) : NativeM α :=
  match computation.match with
  | .ok value => Result.ok value
  | .vis (.fail .panic) _ => fail .panic
  | _ => .error .exhausted

instance : MonadLift RustM NativeM where
  monadLift := fromRust

@[simp] theorem monadLift_eq {α : Type} (computation : RustM α) :
    (monadLift computation : NativeM α) = fromRust computation := rfl

@[simp] theorem fromRust_ok {α : Type} (value : α) :
    fromRust (RustM.ok value) = Result.ok value := by
  simp [fromRust]

@[simp] theorem fromRust_panic {α : Type} :
    fromRust (RustM.fail .panic : RustM α) = fail .panic := by
  simp [fromRust]

@[simp] theorem fromRust_undef {α : Type} :
    fromRust (RustM.fail .undef : RustM α) = Result.error .exhausted := by
  simp [fromRust]

@[simp] theorem fromRust_div {α : Type} :
    fromRust (RustM.div : RustM α) = Result.error .exhausted := by
  simp [fromRust]

/-- Interpreting after composition agrees with composing interpreted primitives. -/
theorem fromRust_bind {α β : Type} (computation : RustM α) (next : α → RustM β) :
    fromRust (computation >>= next) =
      (fromRust computation >>= fun value => fromRust (next value)) := by
  cases computation with
  | ret value => simp
  | div => simp [fromRust]
  | vis effect continuation =>
    cases effect with
    | fail error => cases error <;> simp [fromRust, fail]

@[simp] theorem fromRust_massert (condition : Prop) [Decidable condition] :
    fromRust (Aeneas.Std.massert condition) = massert condition := by
  by_cases accepted : condition <;> simp [Aeneas.Std.massert, massert, accepted]

end NativeM
end Lynx

namespace Lynx

/-- A lossless internal representation for native heap contents. This is not a
Rustler Encoder/Decoder and makes no claim about Rust's in-memory layout. -/
class NativeCodec (α : Type) where
  typeName : String
  encode : α → Term
  decode : Term → Option α
  decode_encode : ∀ value, decode (encode value) = some value

namespace NativeCodec

@[simp] theorem roundtrip {α : Type} [NativeCodec α] (value : α) :
    decode (encode value) = some value := decode_encode value

instance : NativeCodec Bool where
  typeName := "bool"
  encode value := if value then .atom "true" else .atom "false"
  decode value := match value with
    | .atom "true" => some true
    | .atom "false" => some false
    | _ => none
  decode_encode value := by cases value <;> rfl

instance {ty : UScalarTy} : NativeCodec (UScalar ty) where
  typeName := match ty with
    | .U8 => "u8" | .U16 => "u16" | .U32 => "u32"
    | .U64 => "u64" | .U128 => "u128" | .Usize => "usize"
  encode value := .integer value.val
  decode value := match value with
    | .integer value => if valid : 0 ≤ value ∧ value.toNat < 2 ^ ty.numBits then
        some (UScalar.ofNatCore value.toNat valid.2) else none
    | _ => none
  decode_encode value := by
    simp only [Int.natCast_nonneg, Int.toNat_natCast, true_and, value.hmax, ↓reduceDIte]
    congr 1

theorem encode_unsigned {ty : UScalarTy} (value : UScalar ty) :
    encode value = .integer value.val := rfl

theorem decode_unsigned {ty : UScalarTy} (value : Int) :
    decode (α := UScalar ty) (.integer value) =
      if valid : 0 ≤ value ∧ value.toNat < 2 ^ ty.numBits then
        some (UScalar.ofNatCore value.toNat valid.2) else none := rfl

theorem decode_unsigned_invalid {ty : UScalarTy} (value : Int)
    (invalid : ¬ (0 ≤ value ∧ value.toNat < 2 ^ ty.numBits)) :
    decode (α := UScalar ty) (.integer value) = none := by
  rw [decode_unsigned, dite_eq_right invalid]

end NativeCodec

namespace NativeM

/-- Allocate a logical cell without overwriting a prior identity. Physical
allocation and the native primitive's implementation remain trusted models. -/
@[expose] def allocate (typeName : String) (value : Term) : NativeM Nat :=
  .get fun env =>
    let id := env.refCounter + 1
    if env.nativeHeap.any (fun cell => cell.1 == id) then .error .exhausted
    else .set { env with refCounter := id, nativeHeap := (id, typeName, value) :: env.nativeHeap }
      (.ok id)

/-- Wrong-type, missing and ambiguous identities exhaust verification. This
helper is not a Rustler resource decoder or an Elixir-visible failure. -/
@[expose] def readCell (typeName : String) (id : Nat) : NativeM Term :=
  .get fun env =>
    match env.nativeHeap.filter (fun cell => cell.1 == id) with
    | [(_, storedType, value)] =>
      if storedType == typeName then .ok value else .error .exhausted
    | _ => .error .exhausted

@[simp] theorem allocate_run (typeName : String) (value : Term) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    allocate typeName value env =
      (.ok (env.refCounter + 1), { env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1, typeName, value) :: env.nativeHeap }) := by
  simp [allocate, fresh]

@[simp] theorem readCell_run (typeName : String) (id : Nat) (value : Term) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == id) = [(id, typeName, value)]) :
    readCell typeName id env = (.ok value, env) := by
  simp [readCell, stored]

/-- Consume a unique typed cell. The caller must establish the destructor's
payload/ownership requirements; malformed identities exhaust verification. -/
@[expose] def removeCell (typeName : String) (id : Nat) : NativeM Term :=
  .get fun env =>
    match env.nativeHeap.filter (fun cell => cell.1 == id) with
    | [(_, storedType, value)] =>
      if storedType == typeName then
        .set { env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != id) } (.ok value)
      else .error .exhausted
    | _ => .error .exhausted

end NativeM

/-- Movable logical mutex identity. Mutable payloads live in the shared heap. -/
structure NativeMutex (α : Type) where
  id : Nat

namespace NativeMutex

@[expose] def typeName (α : Type) [NativeCodec α] : String :=
  "std::sync::Mutex<" ++ NativeCodec.typeName (α := α) ++ ">"

instance {α : Type} [NativeCodec α] : NativeCodec (NativeMutex α) where
  typeName := NativeMutex.typeName α
  encode mutex := .reference mutex.id
  decode
    | .reference id => some ⟨id⟩
    | _ => none
  decode_encode mutex := by cases mutex; rfl

/-- Model only the initialization of a fresh unlocked, unpoisoned mutex. -/
@[expose] def new {α : Type} [NativeCodec α] (value : α) : NativeM (NativeMutex α) := do
  let id ← NativeM.allocate (typeName α)
    (.tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])
  return { id }

@[simp] theorem new_run {α : Type} [NativeCodec α] (value : α) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    new value env =
      (.ok ⟨env.refCounter + 1⟩, { env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1, typeName α,
          .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value]) :: env.nativeHeap }) := by
  simp [new, NativeM.allocate, fresh]

/-- Destruction of an owned unlocked mutex. Admission separately restricts the
payload to scalars or compiler-certified destructor-free structs. -/
@[expose] def dispose {α : Type} [NativeCodec α] (mutex : NativeMutex α) : NativeM Unit := do
  let contents ← NativeM.readCell (typeName α) mutex.id
  match contents with
  | .tuple fields =>
    if size : fields.size = 3 then
      let lockState := fields[0]'(by omega)
      let poisonState := fields[1]'(by omega)
      let payload := fields[2]'(by omega)
      if lockState == .atom "unlocked" && poisonState == .atom "unpoisoned" then
        match NativeCodec.decode (α := α) payload with
        | some _ =>
          let _ ← NativeM.removeCell (typeName α) mutex.id
          return ()
        | none => .error .exhausted
      else .error .exhausted
    else .error .exhausted
  | _ => .error .exhausted

/-- Creating then consuming an owned destructor-free mutex reclaims its cell
without reusing its identity. Rust admission separately checks payload drops. -/
theorem new_dispose_next {α β : Type} [NativeCodec α] (value : α)
    (next : NativeM β) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    ((do let mutex ← new value; dispose mutex; next) : NativeM β) env =
      next { env with refCounter := env.refCounter + 1 } := by
  have absent : env.nativeHeap.filter (fun cell => cell.1 == env.refCounter + 1) = [] := by
    simpa only [List.filter_eq_nil_iff, List.any_eq_false] using fresh
  have kept : env.nativeHeap.filter (fun cell => cell.1 != env.refCounter + 1) = env.nativeHeap := by
    apply List.filter_eq_self.mpr
    intro cell member
    have unused := (List.any_eq_false.mp fresh) cell member
    simpa using unused
  simp [new, NativeM.allocate, dispose, NativeM.readCell, NativeM.removeCell,
    fresh, absent, kept, NativeCodec.roundtrip]

theorem new_dispose {α : Type} [NativeCodec α] (value : α) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    ((new value >>= dispose) : NativeM Unit) env =
      (.ok (), { env with refCounter := env.refCounter + 1 }) := by
  have unit_id : (fun _ : Unit => (Result.ok () : NativeM Unit)) = Result.ok := by
    funext token
    cases token
    rfl
  simpa only [unit_id, Result.bind_ok, Result.ok_apply] using
    new_dispose_next value (Result.ok ()) env fresh

end NativeMutex
end Lynx

namespace Lynx

/-- Consuming destruction selected by audited Rust call sites. An instance is
not a proof of an arbitrary Rust destructor. -/
class NativeDrop (α : Type) where
  drop : α → NativeM Unit

instance {α : Type} [NativeCodec α] : NativeDrop (NativeMutex α) where
  drop := NativeMutex.dispose

end Lynx

namespace Lynx

/-- An acquisition owns a unique token and a borrowed payload view. The payload
is a value model; mutable-borrow updates must be reconstructed before release. -/
structure NativeGuard (α : Type) where
  mutex : NativeMutex α
  token : Nat
  ownerContext : PID
  value : α

/-- Rust's poisoned acquisition owns the acquired guard, rather than failing
before acquisition. This is not an Elixir exception. -/
structure NativePoisonError (α : Type) where
  value : α

/-- Consuming a poisoned result transfers its payload and leaves poison status
in the shared cell unchanged. It does not release an owned guard. -/
@[expose] def NativePoisonError.into_inner {α : Type} (error : NativePoisonError α) : α :=
  error.value

namespace NativeGuard

/-- Shared borrowing observes the guard's payload view. -/
@[expose] def deref {α : Type} (guard : NativeGuard α) : α := guard.value

/-- Ending a mutable borrow reconstructs the owner with its latest payload.
This does not release the mutex or commit a payload to its shared cell. -/
@[expose] def deref_mut {α : Type} (guard : NativeGuard α) :
    α × (α → NativeGuard α) :=
  (guard.value, fun value => { guard with value })

end NativeGuard

namespace NativeMutex

/-- Atomically inspect and acquire a typed shared cell. Another execution
context's lock blocks; recursive acquisition and invalid cells exhaust the
supported model. OS mutex, thread migration and FFI correctness are unverified. -/
@[expose] def pollLock {α : Type} [NativeCodec α] (mutex : NativeMutex α)
    (env : Environment) : Option (Except Exception
      (core.result.Result (NativeGuard α) (NativePoisonError (NativeGuard α))) × Environment) :=
  let invalid := some (.error .exhausted, env)
  match env.nativeHeap.filter (fun cell => cell.1 == mutex.id) with
  | [(_, storedType, .tuple fields)] =>
    if storedType == typeName α then
      if size : fields.size = 3 then
        let lockState := fields[0]'(by omega)
        let poisonState := fields[1]'(by omega)
        let payload := fields[2]'(by omega)
        match poisonState with
        | .atom poison =>
          if poison == "unpoisoned" || poison == "poisoned" then
            match NativeCodec.decode (α := α) payload with
            | none => invalid
            | some value =>
              match lockState with
              | .atom "unlocked" =>
                let token := env.refCounter + 1
                if env.nativeHeap.any (fun cell => cell.1 == token) then invalid else
                let guard : NativeGuard α := ⟨mutex, token, env.currentPid, value⟩
                let contents := .tuple #[.tuple #[.atom "locked", .pid env.currentPid, .reference token],
                  poisonState, payload]
                let updated := { env with refCounter := token, nativeHeap := env.nativeHeap.map fun cell =>
                  if cell.1 == mutex.id then (mutex.id, typeName α, contents) else cell }
                some (.ok (if poison == "poisoned" then .Err ⟨guard⟩ else .Ok guard), updated)
              | .tuple owner =>
                if ownerSize : owner.size = 3 then
                  let marker := owner[0]'(by omega)
                  let context := owner[1]'(by omega)
                  let token := owner[2]'(by omega)
                  match marker, context, token with
                  | .atom "locked", .pid current, .reference _ =>
                    if current == env.currentPid then invalid else none
                  | _, _, _ => invalid
                else invalid
              | _ => invalid
          else invalid
        | _ => invalid
      else invalid
    else invalid
  | _ => invalid

/-- Blocking acquisition shares the existing scheduler's atomic state waits.
Successful poisoned acquisitions return an error containing the owned guard. -/
@[expose] def lock {α : Type} [NativeCodec α] (mutex : NativeMutex α) :
    NativeM (core.result.Result (NativeGuard α) (NativePoisonError (NativeGuard α))) :=
  .wait (pollLock mutex) fun reply => match reply with
    | .ok result => .ok result
    | .error exception => .error exception

end NativeMutex
end Lynx

namespace Lynx.NativeMutex

/-- The locked representation records an acquisition token and its execution
context; aliases of the same mutex refer to this one shared state. -/
@[expose] def lockedContents {α : Type} [NativeCodec α]
    (context : PID) (token : Nat) (poisoned : Bool) (value : α) : Term :=
  .tuple #[.tuple #[.atom "locked", .pid context, .reference token],
    .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value]

/-- Acquisition preserves unrelated cells and returns ownership even when poisoned. -/
theorem pollLock_unlocked {α : Type} [NativeCodec α] (mutex : NativeMutex α)
    (value : α) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, typeName α, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    pollLock mutex env = some (.ok (
      if poisoned then .Err ⟨⟨mutex, env.refCounter + 1, env.currentPid, value⟩⟩
      else .Ok ⟨mutex, env.refCounter + 1, env.currentPid, value⟩),
      { env with
        refCounter := env.refCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, typeName α, lockedContents env.currentPid (env.refCounter + 1) poisoned value)
          else cell }) := by
  cases poisoned <;> simp [pollLock, stored, fresh, NativeCodec.roundtrip, lockedContents]

/-- In a standalone computation a ready acquisition returns its owned guard. -/
theorem lock_unlocked {α : Type} [NativeCodec α] (mutex : NativeMutex α)
    (value : α) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, typeName α, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    lock mutex env = (.ok (
      if poisoned then .Err ⟨⟨mutex, env.refCounter + 1, env.currentPid, value⟩⟩
      else .Ok ⟨mutex, env.refCounter + 1, env.currentPid, value⟩),
      { env with
        refCounter := env.refCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, typeName α, lockedContents env.currentPid (env.refCounter + 1) poisoned value)
          else cell }) := by
  unfold lock
  rw [Result.wait_ready_apply _ _ _ _ _ (pollLock_unlocked mutex value poisoned env stored fresh)]
  simp

end Lynx.NativeMutex

namespace Lynx.NativeGuard

/-- Commit the reconstructed payload and unlock only the uniquely owned cell.
Normal release preserves poison status. Unwind poisoning requires a separate
execution context and is not implemented by this operation. -/
@[expose] def pollRelease {α : Type} [NativeCodec α] (guard : NativeGuard α)
    (env : Environment) : Option (Except Exception Unit × Environment) :=
  let invalid := some (.error .exhausted, env)
  match env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) with
  | [(_, storedType, .tuple fields)] =>
    if storedType == NativeMutex.typeName α then
      if size : fields.size = 3 then
        let lockState := fields[0]'(by omega)
        let poisonState := fields[1]'(by omega)
        let payload := fields[2]'(by omega)
        match lockState, poisonState with
        | .tuple lockFields, .atom poison =>
          if lockSize : lockFields.size = 3 then
            let marker := lockFields[0]'(by omega)
            let context := lockFields[1]'(by omega)
            let token := lockFields[2]'(by omega)
            match marker, context, token with
            | .atom "locked", .pid owner, .reference token =>
              if owner == guard.ownerContext && token == guard.token &&
                  guard.ownerContext == env.currentPid &&
                  (poison == "unpoisoned" || poison == "poisoned") then
                match NativeCodec.decode (α := α) payload with
                | some _ =>
                  some (.ok (), { env with nativeHeap := env.nativeHeap.map fun cell =>
                    if cell.1 == guard.mutex.id then
                      (guard.mutex.id, NativeMutex.typeName α,
                        .tuple #[.atom "unlocked", .atom poison, NativeCodec.encode guard.value])
                    else cell })
                | none => invalid
              else invalid
            | _, _, _ => invalid
          else invalid
        | _, _ => invalid
      else invalid
    else invalid
  | _ => invalid

@[expose] def release {α : Type} [NativeCodec α] (guard : NativeGuard α) : NativeM Unit :=
  .wait (pollRelease guard) fun reply => match reply with
    | .ok value => .ok value
    | .error error => .error error

/-- Release stores the latest reconstructed borrow, preserving unrelated cells. -/
theorem release_owned {α : Type} [NativeCodec α] (guard : NativeGuard α)
    (original : α) (poisoned : Bool) (env : Environment)
    (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName α,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    release guard env = (.ok (), { env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName α, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode guard.value])
      else cell }) := by
  have ready : pollRelease guard env = some (.ok (), { env with
      nativeHeap := env.nativeHeap.map fun cell => if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName α, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode guard.value])
        else cell }) := by
    cases poisoned <;> simp [pollRelease, NativeMutex.lockedContents, stored, owner,
      NativeCodec.roundtrip]
  unfold release
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

end Lynx.NativeGuard

namespace Lynx
instance {α : Type} [NativeCodec α] : NativeDrop (NativeGuard α) where
  drop := NativeGuard.release
end Lynx

namespace Lynx.NativeGuard

theorem release_owned_next {α β : Type} [NativeCodec α] (guard : NativeGuard α)
    (original : α) (poisoned : Bool) (next : NativeM β) (env : Environment)
    (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName α,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    (do release guard; next) env = next { env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName α, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode guard.value])
      else cell } := by
  have ready : pollRelease guard env = some (.ok (), { env with
      nativeHeap := env.nativeHeap.map fun cell => if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName α, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode guard.value])
        else cell }) := by
    cases poisoned <;> simp [pollRelease, NativeMutex.lockedContents, stored, owner,
      NativeCodec.roundtrip]
  unfold release
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

theorem release_owned_handled_next {α β γ : Type} [NativeCodec α] (guard : NativeGuard α)
    (original : α) (poisoned : Bool) (finish : NativeM β)
    (handler : Exception → NativeM β) (next : β → NativeM γ) (env : Environment)
    (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName α,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    ((Result.handle (do release guard; finish) handler) >>= next) env =
      ((Result.handle finish handler) >>= next) { env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName α, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode guard.value])
      else cell } := by
  have ready : pollRelease guard env = some (.ok (), { env with
      nativeHeap := env.nativeHeap.map fun cell => if cell.1 == guard.mutex.id then
        (guard.mutex.id, NativeMutex.typeName α, .tuple #[.atom "unlocked",
          .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode guard.value])
        else cell }) := by
    cases poisoned <;> simp [pollRelease, NativeMutex.lockedContents, stored, owner,
      NativeCodec.roundtrip]
  unfold release
  simp only [Result.wait_bind, Result.handle]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

end Lynx.NativeGuard

namespace Lynx

/-- One linear Rust reference to a shared resource. Payloads reside in the heap,
not in individual handles. VM-held references require a separate adapter. -/
structure NativeResourceArc (α : Type) where
  id : Nat
  token : Nat

/-- An admitted payload cleanup linked either to compiler-certified absence of
Drop or to the actual extracted owning destructor. No default instance exists. -/
class NativeResourceCleanup (α : Type) where
  cleanup : α → NativeM Unit

/-- Owned-destruction mode uses a separate dispatch with no destructor-free Arc
fallback. Each concrete resource requires a validated payload cleanup instance. -/
class NativeOwnedDrop (α : Type) where
  drop : α → NativeM Unit

instance {α : Type} [NativeCodec α] : NativeOwnedDrop (NativeMutex α) where
  drop := NativeMutex.dispose

instance {α : Type} [NativeCodec α] : NativeOwnedDrop (NativeGuard α) where
  drop := NativeGuard.release

namespace NativeResourceArc

universe u

/-- Rustler 0.39's inherited Resource callback flags are false. Admission checks
the concrete dictionary has no overrides; no user callback is erased here. -/
@[expose, trait_default] def defaultDestructor {ρ : Type u} (_dictionary : ρ) : NativeM Bool := .ok false

@[expose, trait_default] def defaultDown {ρ : Type u} (_dictionary : ρ) : NativeM Bool := .ok false

@[expose] def typeName (α : Type) [NativeCodec α] : String :=
  "resource<" ++ NativeCodec.typeName (α := α) ++ ">"

@[expose] def handleType (α : Type) [NativeCodec α] : String :=
  "resource-handle<" ++ NativeCodec.typeName (α := α) ++ ">"

/-- Verification bound on Rust-owned references, not a simulated VM error. -/
@[expose] def referenceLimit : Nat := 1024

private def payload {α : Type} [NativeCodec α] (contents : Term) : Option (Nat × α) := do
  let .tuple fields := contents | none
  if size : fields.size = 2 then
    let .integer count := (fields[0]'(by omega)) | none
    if 0 < count ∧ count ≤ referenceLimit then
      let value ← NativeCodec.decode (fields[1]'(by omega))
      some (count.toNat, value)
    else none
  else none

private def lookup {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment) : Option (Nat × α) := do
  let [(_, actualHandleType, .reference target)] :=
    env.nativeHeap.filter (fun cell => cell.1 == handle.token) | none
  if actualHandleType != handleType α || target != handle.id then none else
  let [(_, actualType, contents)] :=
    env.nativeHeap.filter (fun cell => cell.1 == handle.id) | none
  if actualType != typeName α then none else
  let (count, value) ← payload contents
  let tokens := env.nativeHeap.filter fun cell =>
    cell.2.1 == handleType α && cell.2.2 == .reference handle.id
  if tokens.length = count then some (count, value) else none

/-- Allocation requires modeled registration, as ResourceArc::new unwraps the
registered type. Physical allocation success is an explicit FFI boundary. -/
@[expose] def new {α : Type} [NativeCodec α] (value : α) : NativeM (NativeResourceArc α) :=
  .get fun env =>
    if typeName α ∈ env.nativeResourceTypes then do
      let id ← NativeM.allocate (typeName α) (.tuple #[.integer 1, NativeCodec.encode value])
      let token ← NativeM.allocate (handleType α) (.reference id)
      .ok ⟨id, token⟩
    else NativeM.fail .panic

/-- Retaining a handle allocates a distinct ownership token for the same cell. -/
def clone {α : Type} [NativeCodec α] (handle : NativeResourceArc α) :
    NativeM (NativeResourceArc α) :=
  .get fun env =>
    match lookup handle env with
    | some (count, value) =>
      let token := env.refCounter + 1
      if count < referenceLimit && !(env.nativeHeap.any (fun cell => cell.1 == token)) then
        .set { env with refCounter := token, nativeHeap :=
          (token, handleType α, .reference handle.id) :: env.nativeHeap.map fun cell =>
            if cell.1 == handle.id then
              (handle.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value])
            else cell }
          (.ok ⟨handle.id, token⟩)
      else .error .exhausted
    | none => .error .exhausted

/-- A shared immutable borrow observes the allocation through its live token. -/
def deref {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM α :=
  .get fun env =>
    match lookup handle env with
    | some (_, value) => .ok value
    | none => .error .exhausted

/-- Consume exactly this Rust ownership token. Admission requires a payload with
no Rust destructor and default resource callbacks. A VM pin is a separate token
and survives release of every Rust-owned handle. -/
def release {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM Unit :=
  .get fun env =>
    match lookup handle env with
    | some (count, value) =>
      let remaining := env.nativeHeap.filter (fun cell => cell.1 != handle.token)
      let heap := if count = 1 then remaining.filter (fun cell => cell.1 != handle.id)
        else remaining.map fun cell => if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer (count - 1), NativeCodec.encode value]) else cell
      .set { env with nativeHeap := heap } (.ok ())
    | none => .error .exhausted

instance {α : Type} [NativeCodec α] : NativeDrop (NativeResourceArc α) where
  drop := release

/-- Registration failure unwinds the still-owned argument before reporting panic.
Physical allocation success and the VM callback remain explicit FFI boundaries. -/
@[expose] def newOwned {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (value : α) : NativeM (NativeResourceArc α) :=
  .get fun env =>
    if typeName α ∈ env.nativeResourceTypes then new value
    else do
      NativeResourceCleanup.cleanup value
      NativeM.fail .panic

/-- Nonfinal release retains the shared payload. Final release runs the admitted
actual cleanup before reclaiming the resource cell and this ownership token. -/
def releaseOwned {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) : NativeM Unit :=
  .get fun env =>
    match lookup handle env with
    | some (count, value) => do
      if count = 1 then NativeResourceCleanup.cleanup value else .ok ()
      release handle
    | none => .error .exhausted

instance {α : Type} [NativeCodec α] [NativeResourceCleanup α] :
    NativeOwnedDrop (NativeResourceArc α) where
  drop := releaseOwned

/-- A validated final token executes payload cleanup before reclaiming the Arc. -/
theorem releaseOwned_last_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 1) :
    (releaseOwned handle >>= next) env =
      (do NativeResourceCleanup.cleanup value; release handle >>= next) env := by
  simp [releaseOwned, lookup, payload, token, stored, owners,
    NativeCodec.roundtrip, referenceLimit]

/-- Releasing one of two validated tokens does not run payload destruction. -/
theorem releaseOwned_retained_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 2) :
    (releaseOwned handle >>= next) env = (release handle >>= next) env := by
  simp [releaseOwned, lookup, payload, token, stored, owners,
    NativeCodec.roundtrip, referenceLimit]

/-- A live resource borrow retains its exact shared payload identity. -/
theorem deref_single_next {α β : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (next : α → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 1) :
    (deref handle >>= next) env = next value env := by
  simp [deref, lookup, payload, token, stored, owners, NativeCodec.roundtrip, referenceLimit]

theorem deref_retained_handled_next {α β γ : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (finish : α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 2) :
    ((Result.handle (deref handle >>= finish) handler) >>= next) env =
      ((Result.handle (finish value) handler) >>= next) env := by
  simp [Result.handle, deref, lookup, payload, token, stored, owners, NativeCodec.roundtrip, referenceLimit]

/-- Retaining a validated sole owner creates another token for the same value. -/
theorem clone_single_next {α β : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (next : NativeResourceArc α → NativeM β)
    (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 1)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.refCounter + 1) = false) :
    (clone handle >>= next) env = next ⟨handle.id, env.refCounter + 1⟩ {env with
      refCounter := env.refCounter + 1, nativeHeap :=
        (env.refCounter + 1, handleType α, .reference handle.id) :: env.nativeHeap.map fun cell =>
          if cell.1 == handle.id then
            (handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value]) else cell } := by
  simp [clone, lookup, payload, token, stored, owners, fresh,
    NativeCodec.roundtrip, referenceLimit]

/-- Consuming a nonfinal token preserves payload cells and the other owner. -/
theorem releaseOwned_retained_run_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 2) :
    (releaseOwned handle >>= next) env = next () {env with nativeHeap :=
      (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value]) else cell } := by
  rw [releaseOwned_retained_next handle value next env token stored owners]
  simp [release, lookup, payload, token, stored, owners, NativeCodec.roundtrip, referenceLimit]

theorem releaseOwned_retained_handled_next {α β γ : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (finish : NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 2) :
    ((Result.handle (do releaseOwned handle; finish) handler) >>= next) env =
      ((Result.handle finish handler) >>= next) {env with nativeHeap :=
      (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value]) else cell } := by
  simp [releaseOwned, release, lookup, payload, token, stored, owners,
    NativeCodec.roundtrip, referenceLimit, Result.handle]

/-- Successful final cleanup may change payload-owned cells, while retaining the
Arc bookkeeping until release consumes it. All other environment fields survive. -/
theorem releaseOwned_last_run_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env after : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 1)
    (cleaned : ∀ next : NativeM β,
      (do NativeResourceCleanup.cleanup value; next) env = next after)
    (tokenAfter : after.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .reference handle.id)])
    (storedAfter : after.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (ownersAfter : (after.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference handle.id).length = 1) :
    (releaseOwned handle >>= next) env = next () {after with nativeHeap :=
      (after.nativeHeap.filter fun cell => cell.1 != handle.token).filter fun cell => cell.1 != handle.id} := by
  rw [releaseOwned_last_next handle value next env token stored owners]
  rw [cleaned (release handle >>= next)]
  simp [release, lookup, payload, tokenAfter, storedAfter, ownersAfter,
    NativeCodec.roundtrip, referenceLimit]

/-- A VM resource term retains a distinct ownership token. Its registry cell is
separate from Rust tokens; repeated encoding of the allocation reuses its term
identity. Physical VM references and garbage collection remain FFI models. -/
@[expose] def termType (α : Type) [NativeCodec α] : String :=
  "resource-term<" ++ NativeCodec.typeName (α := α) ++ ">"

private def termEntryOwner {α : Type} [NativeCodec α]
    (cell : Nat × String × Term) : Option (NativeResourceArc α) := do
  if cell.2.1 != termType α then none else
  let .tuple fields := cell.2.2 | none
  if size : fields.size = 2 then
    let .reference id := (fields[0]'(by omega)) | none
    let .reference token := (fields[1]'(by omega)) | none
    some ⟨id, token⟩
  else none

private def termOwner {α : Type} [NativeCodec α] (term : Term)
    (env : Environment) : Option (NativeResourceArc α) := do
  let .reference identity := term | none
  let [cell] := env.nativeHeap.filter (fun cell => cell.1 == identity) | none
  termEntryOwner cell

/-- Model enif_make_resource: pin the allocation independently of its Rust owner.
Existing live terms for the same allocation share identity. No Rust owner is
consumed by Encoder::encode(&self); the generated wrapper drops it afterwards. -/
def encode {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM Term :=
  .get fun env =>
    match lookup handle env with
    | none => .error .exhausted
    | some _ =>
      let existing := env.nativeHeap.filter fun cell =>
        match termEntryOwner (α := α) cell with
        | some owner => owner.id == handle.id
        | none => false
      match existing with
      | [] => do
        let pin ← clone handle
        let identity ← NativeM.allocate (termType α)
          (.tuple #[.reference pin.id, .reference pin.token])
        .ok (.reference identity)
      | [(identity, _, _)] =>
        match termOwner (α := α) (.reference identity) env with
        | some pin => if (lookup pin env).isSome then .ok (.reference identity)
            else .error .exhausted
        | none => .error .exhausted
      | _ => .error .exhausted

/-- Model ResourceArc::from_term: wrong terms/types produce badarg; a successful
conversion acquires a fresh Rust ownership token while preserving the VM pin.
An inconsistent internal heap is verification exhaustion. -/
def decode {α : Type} [NativeCodec α] (term : Term) : NativeM (NativeResourceArc α) :=
  .get fun env =>
    if typeName α ∈ env.nativeResourceTypes then
      match termOwner term env with
      | none => .error (.error (.atom "badarg"))
      | some pin => clone pin
    else .error (.error (.atom "badarg"))

@[simp] theorem decode_nonreference {α : Type} [NativeCodec α] (term : Term)
    (notReference : ∀ identity, term ≠ .reference identity) (env : Environment) :
    decode (α := α) term env = (.error (.error (.atom "badarg")), env) := by
  by_cases registered : typeName α ∈ env.nativeResourceTypes
  · cases term <;> simp_all [decode, termOwner]
  · simp [decode, registered]

/-- Rustler cannot recover a typed resource before its type is registered. -/
theorem decode_unregistered {α : Type} [NativeCodec α] (term : Term) (env : Environment)
    (absent : typeName α ∉ env.nativeResourceTypes) :
    decode (α := α) term env = (.error (.error (.atom "badarg")), env) := by
  simp [decode, absent]

/-- An ordinary reference without a resource registry cell is not a resource. -/
theorem decode_missing {α : Type} [NativeCodec α] (identity : Nat) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == identity) = []) :
    decode (α := α) (.reference identity) env =
      (.error (.error (.atom "badarg")), env) := by
  by_cases registered : typeName α ∈ env.nativeResourceTypes <;>
    simp [decode, registered, termOwner, missing]

/-- A reference belonging to another nominal resource type cannot decode. -/
theorem decode_wrong_type {α : Type} [NativeCodec α] (identity : Nat)
    (env : Environment) (tag : String) (contents : Term)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == identity) = [(identity, tag, contents)])
    (different : tag ≠ termType α) :
    decode (α := α) (.reference identity) env =
      (.error (.error (.atom "badarg")), env) := by
  by_cases registered : typeName α ∈ env.nativeResourceTypes
  · cases contents <;> simp [decode, registered, termOwner, termEntryOwner, stored, different]
  · simp [decode, registered]

/-- An absent loader registration produces Rustler's constructor panic. -/
theorem new_unregistered {α : Type} [NativeCodec α] (value : α) (env : Environment)
    (absent : typeName α ∉ env.nativeResourceTypes) :
    new value env = (.error (.error (.atom "rust_panicked")), env) := by
  simp [new, absent, NativeM.fail]

/-- A consumed or absent ownership token cannot observe a resource. This is
verification exhaustion, not an Elixir-visible badarg result. -/
theorem deref_missing {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    deref handle env = (.error .exhausted, env) := by
  simp [deref, lookup, missing]

theorem clone_missing {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    clone handle env = (.error .exhausted, env) := by
  simp [clone, lookup, missing]

/-- Releasing an already consumed token cannot decrement another owner's count. -/
theorem release_missing {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    release handle env = (.error .exhausted, env) := by
  simp [release, lookup, missing]

/-- A forged count cannot keep a resource alive without the corresponding owners. -/
theorem deref_inconsistent_count {α : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (env : Environment)
    (distinct : handle.id ≠ handle.token)
    (stored : env.nativeHeap = [
      (handle.token, handleType α, .reference handle.id),
      (handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])]) :
    deref handle env = (.error .exhausted, env) := by
  simp [deref, lookup, payload, stored, distinct, Ne.symm distinct,
    NativeCodec.roundtrip, referenceLimit, handleType, typeName]

/-- Clone retains the allocation after the original owner is consumed. Final
release removes both the last token and allocation; other runtime fields survive. -/
theorem clone_release_cycle_next {α β : Type} [NativeCodec α] (value : α)
    (next : α → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    (do
      let first ← new value
      let retained ← clone first
      release first
      let observed ← deref retained
      release retained
      next observed) env = next value { env with refCounter := env.refCounter + 3 } := by
  simp only [new, Result.get_bind, Result.get_continuation_apply, ite_eq_left registered]
  simp [clone, release, deref, lookup, payload, NativeM.allocate,
    empty, NativeCodec.roundtrip, referenceLimit, handleType, typeName, Nat.add_assoc]

theorem clone_release_cycle {α : Type} [NativeCodec α] (value : α) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes) (empty : env.nativeHeap = []) :
    (do
      let first ← new value
      let retained ← clone first
      release first
      let observed ← deref retained
      release retained
      Result.ok observed) env =
        (.ok value, { env with refCounter := env.refCounter + 3 }) := by
  simpa using clone_release_cycle_next value Result.ok env registered empty

/-- Native exception conversion and a caller continuation retain final cleanup.
The handler remains outside all lifecycle operations; no panic is discarded. -/
theorem clone_release_cycle_handled_next {α β γ : Type} [NativeCodec α] (value : α)
    (finish : α → NativeM β) (handler : Exception → NativeM β) (next : β → NativeM γ)
    (env : Environment) (registered : typeName α ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    ((Result.handle (do
      let first ← new value
      let retained ← clone first
      release first
      let observed ← deref retained
      release retained
      finish observed) handler) >>= next) env =
      ((Result.handle (finish value) handler) >>= next)
        { env with refCounter := env.refCounter + 3 } := by
  simp only [new, Result.get_bind, Result.handle, Result.get_continuation_apply,
    ite_eq_left registered]
  simp [clone, release, deref, lookup, payload, NativeM.allocate, Result.handle,
    empty, NativeCodec.roundtrip, referenceLimit, handleType, typeName, Nat.add_assoc]

set_option maxHeartbeats 800000 in
/-- A VM pin survives dropping both Rust owners. Repeated encoding preserves
term identity and decoding creates an independent Rust owner. The remaining
VM pin is retained explicitly; automatic garbage collection is not modeled. -/
theorem vm_roundtrip_next {α β : Type} [NativeCodec α] (value : α)
    (next : α → Bool → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes) (empty : env.nativeHeap = []) :
    (do
      let original ← new value
      let term ← encode original
      let again ← encode original
      release original
      let decoded ← decode (α := α) term
      let observed ← deref decoded
      release decoded
      next observed (term == again)) env = next value true { env with refCounter := env.refCounter + 5, nativeHeap := [
        (env.refCounter + 4, termType α,
          .tuple #[.reference (env.refCounter + 1), .reference (env.refCounter + 3)]),
        (env.refCounter + 3, handleType α, .reference (env.refCounter + 1)),
        (env.refCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])] } := by
  simp only [new, Result.get_bind, Result.get_continuation_apply, ite_eq_left registered]
  simp only [typeName] at registered
  simp [encode, decode, termOwner, termEntryOwner, clone, release, deref, lookup, payload,
    NativeM.allocate, empty, NativeCodec.roundtrip, referenceLimit, handleType,
    typeName, termType, registered, Nat.add_assoc]

/-- A resource-visible frame cannot refer to identities above this counter.
Payload contents are opaque: only ownership tokens and VM registry references
are inspected by resource operations. This is not whole-runtime reachability. -/
@[expose] def FrameBelow (α : Type) [NativeCodec α] (limit : Nat)
    (frame : List (Nat × String × Term)) : Prop :=
  ∀ cell ∈ frame, cell.1 ≤ limit ∧
    (cell.2.1 = handleType α → ∀ target, cell.2.2 = .reference target → target ≤ limit) ∧
    (cell.2.1 = termType α → ∀ fields, cell.2.2 = .tuple fields →
      ∀ target, Term.reference target ∈ fields.toList → target ≤ limit)

/-- The three logical cells retained by an encoded immutable resource. -/
@[expose] def vmCells {α : Type} [NativeCodec α] (value : α) (id pin term : Nat) :
    List (Nat × String × Term) := [
  (term, termType α, .tuple #[.reference id, .reference pin]),
  (pin, handleType α, .reference id),
  (id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])]

theorem FrameBelow.mono {α : Type} [NativeCodec α] {lower upper : Nat}
    {frame : List (Nat × String × Term)} (bounded : FrameBelow α lower frame)
    (larger : lower ≤ upper) : FrameBelow α upper frame := by
  intro cell member
  have facts := bounded cell member
  refine ⟨Nat.le_trans facts.1 larger, ?_, ?_⟩
  · intro tag target contents
    exact Nat.le_trans (facts.2.1 tag target contents) larger
  · intro tag fields contents target member
    exact Nat.le_trans (facts.2.2 tag fields contents target member) larger

theorem FrameBelow.append {α : Type} [NativeCodec α] {limit : Nat}
    {first second : List (Nat × String × Term)}
    (left : FrameBelow α limit first) (right : FrameBelow α limit second) :
    FrameBelow α limit (first ++ second) := by
  intro cell member
  rcases List.mem_append.mp member with member | member
  · exact left cell member
  · exact right cell member

theorem FrameBelow.vmCells {α : Type} [NativeCodec α] (value : α) (id pin term limit : Nat)
    (bounds : id ≤ limit ∧ pin ≤ limit ∧ term ≤ limit) :
    FrameBelow α limit (NativeResourceArc.vmCells value id pin term) := by
  intro cell member
  simp only [NativeResourceArc.vmCells, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp_all [typeName, handleType, termType]

private theorem frame_filter_id (frame : List (Nat × String × Term)) (limit id : Nat)
    (bounded : ∀ cell ∈ frame, cell.1 ≤ limit) (fresh : limit < id) :
    frame.filter (fun cell => cell.1 == id) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  have := bounded cell member
  simp only [beq_iff_eq]
  omega

private theorem frame_filter_ne (frame : List (Nat × String × Term)) (limit id : Nat)
    (bounded : ∀ cell ∈ frame, cell.1 ≤ limit) (fresh : limit < id) :
    frame.filter (fun cell => cell.1 != id) = frame := by
  apply List.filter_eq_self.mpr
  intro cell member
  have := bounded cell member
  simp only [bne_iff_ne]
  omega

private theorem frame_map_update (frame : List (Nat × String × Term)) (limit id : Nat)
    (update : (Nat × String × Term) → (Nat × String × Term))
    (bounded : ∀ cell ∈ frame, cell.1 ≤ limit) (fresh : limit < id) :
    frame.map (fun cell => if cell.1 == id then update cell else cell) = frame := by
  calc
    _ = frame.map (fun cell => cell) := List.map_congr_left (by
      intro cell member
      have bound := bounded cell member
      have different : cell.1 ≠ id := by omega
      simp [different])
    _ = frame := List.map_id' frame

private theorem frame_any_id (frame : List (Nat × String × Term)) (limit id : Nat)
    (bounded : ∀ cell ∈ frame, cell.1 ≤ limit) (fresh : limit < id) :
    frame.any (fun cell => cell.1 == id) = false := by
  simp only [List.any_eq_false]
  intro cell member
  have := bounded cell member
  simp only [beq_iff_eq]
  omega

private theorem beq_reference (value : Term) (id : Nat) :
    (value == .reference id) = true ↔ value = .reference id := by
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]

private theorem frame_tokens (frame : List (Nat × String × Term)) (limit id : Nat)
    {α : Type} [NativeCodec α] (bounded : FrameBelow α limit frame) (fresh : limit < id) :
    frame.filter (fun cell => cell.2.1 == handleType α && cell.2.2 == .reference id) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  have bound := (bounded cell member).2.1
  simp only [Bool.and_eq_true, beq_iff_eq, beq_reference]
  rintro ⟨tag, contents⟩
  have := bound tag id contents
  omega

private theorem frame_owner_bound (frame : List (Nat × String × Term)) (limit : Nat)
    {α : Type} [NativeCodec α] (bounded : FrameBelow α limit frame)
    (cell : Nat × String × Term) (member : cell ∈ frame) (owner : NativeResourceArc α)
    (found : termEntryOwner cell = some owner) : owner.id ≤ limit := by
  have bound := (bounded cell member).2.2
  unfold termEntryOwner at found
  split at found
  · simp_all
  · rename_i tag
    have tagEq : cell.2.1 = termType α := by simpa using tag
    split at found
    · rename_i fields shape
      split at found
      · rename_i size
        split at found
        · rename_i target first
          split at found
          · rename_i token second
            cases found
            exact bound tagEq fields shape target (by
              simp only [_root_.Array.mem_toList_iff]
              exact _root_.Array.mem_of_getElem first)
          · simp_all
        · simp_all
      · simp_all
    · simp_all

private theorem frame_terms (frame : List (Nat × String × Term)) (limit id : Nat)
    {α : Type} [NativeCodec α] (bounded : FrameBelow α limit frame) (fresh : limit < id) :
    frame.filter (fun cell => match termEntryOwner (α := α) cell with
      | some owner => owner.id == id
      | none => false) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  cases found : termEntryOwner (α := α) cell with
  | none => simp
  | some owner =>
    have := frame_owner_bound frame limit bounded cell member owner found
    simp only [beq_iff_eq]
    omega

/-- An immutable VM-held allocation, described by keyed views of the heap.
Other allocations may occur anywhere in the list. No other Rust owner of this
allocation is live at this NIF boundary. -/
structure Pinned {α : Type} [NativeCodec α] (value : α) (id pin term : Nat)
    (env : Environment) : Prop where
  ordered : id < pin ∧ pin < term ∧ term ≤ env.refCounter
  keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.refCounter
  allocation : env.nativeHeap.filter (fun cell => cell.1 == id) =
    [(id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])]
  owner : env.nativeHeap.filter (fun cell => cell.1 == pin) =
    [(pin, handleType α, .reference id)]
  registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
    [(term, termType α, .tuple #[.reference id, .reference pin])]
  owners : (env.nativeHeap.filter (fun cell =>
    cell.2.1 == handleType α && cell.2.2 == .reference id)).length = 1

private abbrev replaceCell (id : Nat) (tag : String) (contents : Term)
    (cell : Nat × String × Term) :=
  if cell.1 == id then (id, tag, contents) else cell

private theorem replaceCell_fun (id : Nat) (tag : String) (contents : Term) :
    replaceCell id tag contents = (fun cell => if cell.1 == id then (id, tag, contents) else cell) := rfl

private theorem replaceCell_key (id : Nat) (tag : String) (contents : Term)
    (cell : Nat × String × Term) : (replaceCell id tag contents cell).1 = cell.1 := by
  unfold replaceCell
  split
  · rename_i same
    exact (show cell.1 = id from by simpa using same).symm
  · rfl

private theorem filter_replace (heap : List (Nat × String × Term))
    (id key : Nat) (tag : String) (contents : Term) :
    (heap.map (replaceCell id tag contents)).filter (fun cell => cell.1 == key) =
      (heap.filter (fun cell => cell.1 == key)).map (replaceCell id tag contents) := by
  simp only [List.filter_map, Function.comp_def, replaceCell_key]

private theorem filter_ne_replace (heap : List (Nat × String × Term))
    (id key : Nat) (tag : String) (contents : Term) :
    (heap.map (replaceCell id tag contents)).filter (fun cell => cell.1 != key) =
      (heap.filter (fun cell => cell.1 != key)).map (replaceCell id tag contents) := by
  simp only [List.filter_map, Function.comp_def, replaceCell_key]

private theorem known_cell (heap : List (Nat × String × Term)) (id : Nat)
    (tag : String) (contents : Term)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id, tag, contents)])
    (cell : Nat × String × Term) (member : cell ∈ heap) (same : cell.1 = id) :
    cell = (id, tag, contents) := by
  have included : cell ∈ heap.filter (fun cell => cell.1 == id) :=
    List.mem_filter.mpr ⟨member, by simp [same]⟩
  simpa [stored] using included

private theorem replace_restore (heap : List (Nat × String × Term)) (id : Nat)
    (tag : String) (before after : Term)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id, tag, before)]) :
    (heap.map (replaceCell id tag after)).map (replaceCell id tag before) = heap := by
  rw [List.map_map]
  calc
    _ = heap.map (fun cell => cell) := List.map_congr_left (by
      intro cell member
      by_cases same : cell.1 = id
      · have equal := known_cell heap id tag before stored cell member same
        subst cell
        simp [replaceCell]
      · simp [replaceCell, same])
    _ = heap := List.map_id' heap

private theorem replace_token_count {α : Type} [NativeCodec α]
    (heap : List (Nat × String × Term)) (id : Nat) (before after : Term)
    (stored : heap.filter (fun cell => cell.1 == id) = [(id, typeName α, before)]) :
    ((heap.map (replaceCell id (typeName α) after)).filter (fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference id)).length =
    (heap.filter (fun cell => cell.2.1 == handleType α && cell.2.2 == .reference id)).length := by
  rw [List.filter_map, List.length_map]
  congr 1
  apply List.filter_congr
  intro cell member
  by_cases same : cell.1 = id
  · have equal := known_cell heap id (typeName α) before stored cell member same
    subst cell
    have tags : typeName α ≠ handleType α := by
      simp [typeName, handleType, String.append_left_inj]
    have different : (typeName α == handleType α) = false :=
      Bool.eq_false_iff.mpr (by
        intro equal
        exact tags (_root_.beq_iff_eq.mp equal))
    simp [replaceCell, different]
  · simp [replaceCell, same]

set_option maxHeartbeats 1000000 in
/-- Returning a new resource preserves every cell in a bounded resource frame.
No pre-existing owner or VM registry may refer to the newly allocated identities. -/
theorem new_encode_release_framed_next {α β : Type} [NativeCodec α] (value : α)
    (handler : Exception → NativeM Term) (next : Term → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes)
    (frame : FrameBelow α env.refCounter env.nativeHeap) :
    ((Result.handle (do
      let owner ← new value
      let term ← encode owner
      release owner
      Result.ok term) handler) >>= next) env =
    next (.reference (env.refCounter + 4)) { env with
      refCounter := env.refCounter + 4
      nativeHeap := vmCells value (env.refCounter + 1) (env.refCounter + 3)
        (env.refCounter + 4) ++ env.nativeHeap } := by
  have keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.refCounter := fun cell member =>
    (frame cell member).1
  have ids1 := frame_filter_id env.nativeHeap env.refCounter (env.refCounter + 1) keys (by omega)
  have anys1 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 1) keys (by omega)
  have ids2 := frame_filter_id env.nativeHeap env.refCounter (env.refCounter + 2) keys (by omega)
  have anys2 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 2) keys (by omega)
  have anys3 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 3) keys (by omega)
  have anys4 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 4) keys (by omega)
  have removes := frame_filter_ne env.nativeHeap env.refCounter (env.refCounter + 2) keys (by omega)
  have mapTwo := frame_map_update env.nativeHeap env.refCounter (env.refCounter + 1)
    (fun _ => (env.refCounter + 1, typeName α, .tuple #[.integer 2, NativeCodec.encode value])) keys (by omega)
  have mapOne := frame_map_update env.nativeHeap env.refCounter (env.refCounter + 1)
    (fun _ => (env.refCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])) keys (by omega)
  have tokens := frame_tokens env.nativeHeap env.refCounter (env.refCounter + 1) frame (by omega)
  have terms := frame_terms env.nativeHeap env.refCounter (env.refCounter + 1) frame (by omega)
  simp only [handleType] at tokens
  simp only [termEntryOwner, termType, bne_iff_ne, ite_not] at terms
  simp only [typeName, beq_iff_eq] at mapTwo mapOne
  simp only [new, Result.handle, Result.get_bind, Result.get_continuation_apply,
    ite_eq_left registered]
  simp [encode, termOwner, termEntryOwner, clone, release, lookup,
    payload, NativeM.allocate, Result.handle, vmCells, ids1, ids2,
    removes, mapTwo, mapOne, anys1, anys2, anys3, anys4, tokens, terms,
    NativeCodec.roundtrip, referenceLimit,
    handleType, typeName, termType, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
/-- Owned structural cleanup also preserves the VM pin on successful resource return.
No pre-existing owner or VM registry may refer to the newly allocated identities. -/
theorem newOwned_encode_release_framed_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α] (value : α)
    (handler : Exception → NativeM Term) (next : Term → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes)
    (frame : FrameBelow α env.refCounter env.nativeHeap) :
    ((Result.handle (do
      let owner ← newOwned value
      let term ← encode owner
      releaseOwned owner
      Result.ok term) handler) >>= next) env =
    next (.reference (env.refCounter + 4)) { env with
      refCounter := env.refCounter + 4
      nativeHeap := vmCells value (env.refCounter + 1) (env.refCounter + 3)
        (env.refCounter + 4) ++ env.nativeHeap } := by
  have keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.refCounter := fun cell member =>
    (frame cell member).1
  have ids1 := frame_filter_id env.nativeHeap env.refCounter (env.refCounter + 1) keys (by omega)
  have anys1 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 1) keys (by omega)
  have ids2 := frame_filter_id env.nativeHeap env.refCounter (env.refCounter + 2) keys (by omega)
  have anys2 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 2) keys (by omega)
  have anys3 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 3) keys (by omega)
  have anys4 := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 4) keys (by omega)
  have removes := frame_filter_ne env.nativeHeap env.refCounter (env.refCounter + 2) keys (by omega)
  have mapTwo := frame_map_update env.nativeHeap env.refCounter (env.refCounter + 1)
    (fun _ => (env.refCounter + 1, typeName α, .tuple #[.integer 2, NativeCodec.encode value])) keys (by omega)
  have mapOne := frame_map_update env.nativeHeap env.refCounter (env.refCounter + 1)
    (fun _ => (env.refCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])) keys (by omega)
  have tokens := frame_tokens env.nativeHeap env.refCounter (env.refCounter + 1) frame (by omega)
  have terms := frame_terms env.nativeHeap env.refCounter (env.refCounter + 1) frame (by omega)
  simp only [handleType] at tokens
  simp only [termEntryOwner, termType, bne_iff_ne, ite_not] at terms
  simp only [typeName, beq_iff_eq] at mapTwo mapOne
  simp only [newOwned, new, Result.handle, Result.get_bind, Result.get_continuation_apply,
    ite_eq_left registered]
  simp [encode, termOwner, termEntryOwner, clone, releaseOwned, release, lookup,
    payload, NativeM.allocate, Result.handle, vmCells, ids1, ids2,
    removes, mapTwo, mapOne, anys1, anys2, anys3, anys4, tokens, terms,
    NativeCodec.roundtrip, referenceLimit,
    handleType, typeName, termType, Nat.add_assoc]

set_option maxHeartbeats 800000 in
/-- Successful resource return keeps the VM pin after releasing the Rust result.
The native exception handler is retained rather than erased from the adapter. -/
theorem new_encode_release_handled_next {α β : Type} [NativeCodec α] (value : α)
    (handler : Exception → NativeM Term) (next : Term → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes) (empty : env.nativeHeap = []) :
    ((Result.handle (do
      let owner ← new value
      let term ← encode owner
      release owner
      Result.ok term) handler) >>= next) env =
    next (.reference (env.refCounter + 4)) { env with refCounter := env.refCounter + 4, nativeHeap := [
      (env.refCounter + 4, termType α,
        .tuple #[.reference (env.refCounter + 1), .reference (env.refCounter + 3)]),
      (env.refCounter + 3, handleType α, .reference (env.refCounter + 1)),
      (env.refCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])] } := by
  simp only [new, Result.handle, Result.get_bind, Result.get_continuation_apply,
    ite_eq_left registered]
  simp [encode, termOwner, termEntryOwner, clone, release, lookup, payload,
    NativeM.allocate, Result.handle, empty, NativeCodec.roundtrip, referenceLimit,
    handleType, typeName, termType, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
/-- Reading a pinned allocation preserves the complete heap, independent of the
positions and contents of unrelated cells. Only a fresh temporary Rust owner is
allocated and released. -/
theorem decode_read_pinned_next {α β γ : Type} [NativeCodec α]
    (value : α) (finish : α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment) (id pin term : Nat)
    (pinned : Pinned value id pin term env)
    (registered : typeName α ∈ env.nativeResourceTypes) :
    (do
      let owner ← decode (α := α) (.reference term)
      let result ← Result.handle (do
        let observed ← deref owner
        release owner
        finish observed) handler
      next result) env =
      ((Result.handle (finish value) handler) >>= next)
        {env with refCounter := env.refCounter + 1} := by
  have a : id ≠ pin := by have := pinned.ordered; omega
  have b : id ≠ term := by have := pinned.ordered; omega
  have c : pin ≠ term := by have := pinned.ordered; omega
  have d : env.refCounter + 1 ≠ id := by have := pinned.ordered; omega
  have e : env.refCounter + 1 ≠ pin := by have := pinned.ordered; omega
  have f : env.refCounter + 1 ≠ term := by have := pinned.ordered; omega
  let changed := env.nativeHeap.map (replaceCell id (typeName α)
    (.tuple #[.integer 2, NativeCodec.encode value]))
  have allocation2 : changed.filter (fun cell => cell.1 == id) =
      [(id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])] := by
    simp [changed, filter_replace, pinned.allocation, replaceCell]
  have owner2 : changed.filter (fun cell => cell.1 == pin) =
      [(pin, handleType α, .reference id)] := by
    simp [changed, filter_replace, pinned.owner, replaceCell, a, Ne.symm a]
  have fresh := frame_filter_id env.nativeHeap env.refCounter (env.refCounter + 1)
    pinned.keys (by omega)
  have absent2 : changed.filter (fun cell => cell.1 == env.refCounter + 1) = [] := by
    simp [changed, filter_replace, fresh]
  have anyFresh := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 1)
    pinned.keys (by omega)
  have count2 : (changed.filter (fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .reference id)).length = 1 := by
    rw [show changed = _ from rfl, replace_token_count env.nativeHeap id
      (.tuple #[.integer 1, NativeCodec.encode value]) _ pinned.allocation]
    exact pinned.owners
  have removeFresh := frame_filter_ne env.nativeHeap env.refCounter (env.refCounter + 1)
    pinned.keys (by omega)
  have removes : changed.filter (fun cell => cell.1 != env.refCounter + 1) = changed := by
    simp [changed, filter_ne_replace, removeFresh]
  have restores : changed.map (replaceCell id (typeName α)
      (.tuple #[.integer 1, NativeCodec.encode value])) = env.nativeHeap :=
    replace_restore env.nativeHeap id (typeName α) _ _ pinned.allocation
  have allocation := pinned.allocation
  have owner := pinned.owner
  have registry := pinned.registry
  have owners := pinned.owners
  simp only [typeName] at registered
  simp only [typeName, handleType, termType] at allocation owner registry owners
  dsimp only [changed] at allocation2 owner2 absent2 count2 removes restores
  simp only [replaceCell_fun, typeName, handleType, beq_iff_eq] at allocation2 owner2 absent2 count2 removes restores
  simp [decode, registered, termOwner, termEntryOwner, clone, release, deref,
    lookup, payload, Result.handle, allocation, owner, registry, owners,
    allocation2, owner2, absent2, count2, anyFresh, removes, restores,
    NativeCodec.roundtrip, referenceLimit, typeName, handleType, termType,
    a, b, c, d, Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f]

set_option maxHeartbeats 1000000 in
/-- Decode a pinned term before an effectful native computation, retaining both
its temporary Rust token and VM pin. Payload-owned cells are preserved. -/
theorem decode_pinned_next {α β : Type} [NativeCodec α]
    (value : α) (next : NativeResourceArc α → NativeM β)
    (env : Environment) (id pin term : Nat) (pinned : Pinned value id pin term env)
    (registered : typeName α ∈ env.nativeResourceTypes) :
    (decode (α := α) (.reference term) >>= next) env =
      next ⟨id, env.refCounter + 1⟩ { env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1, handleType α, .reference id) ::
          env.nativeHeap.map fun cell => if cell.1 == id then
            (id, typeName α, .tuple #[.integer 2, NativeCodec.encode value]) else cell } := by
  have a : id ≠ pin := by have := pinned.ordered; omega
  have b : id ≠ term := by have := pinned.ordered; omega
  have c : pin ≠ term := by have := pinned.ordered; omega
  have d : env.refCounter + 1 ≠ id := by have := pinned.ordered; omega
  have e : env.refCounter + 1 ≠ pin := by have := pinned.ordered; omega
  have f : env.refCounter + 1 ≠ term := by have := pinned.ordered; omega
  have anyFresh := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 1)
    pinned.keys (by omega)
  have allocation := pinned.allocation
  have owner := pinned.owner
  have registry := pinned.registry
  have owners := pinned.owners
  simp only [typeName] at registered
  simp only [typeName, handleType, termType] at allocation owner registry owners
  simp [decode, registered, termOwner, termEntryOwner, clone, lookup, payload,
    allocation, owner, registry, owners, anyFresh, NativeCodec.roundtrip,
    referenceLimit, typeName, handleType, termType, a, b, c, d, e, f,
    Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f]

theorem decode_pinned_handled_next {α β γ : Type} [NativeCodec α]
    (value : α) (finish : NativeResourceArc α → NativeM β)
    (handler : Exception → NativeM β) (next : β → NativeM γ)
    (env : Environment) (id pin term : Nat) (pinned : Pinned value id pin term env)
    (registered : typeName α ∈ env.nativeResourceTypes) :
    ((Result.handle (decode (α := α) (.reference term) >>= finish) handler) >>= next) env =
      ((Result.handle (finish ⟨id, env.refCounter + 1⟩) handler) >>= next) { env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1, handleType α, .reference id) ::
          env.nativeHeap.map fun cell => if cell.1 == id then
            (id, typeName α, .tuple #[.integer 2, NativeCodec.encode value]) else cell } := by
  have a : id ≠ pin := by have := pinned.ordered; omega
  have b : id ≠ term := by have := pinned.ordered; omega
  have c : pin ≠ term := by have := pinned.ordered; omega
  have d : env.refCounter + 1 ≠ id := by have := pinned.ordered; omega
  have e : env.refCounter + 1 ≠ pin := by have := pinned.ordered; omega
  have f : env.refCounter + 1 ≠ term := by have := pinned.ordered; omega
  have anyFresh := frame_any_id env.nativeHeap env.refCounter (env.refCounter + 1)
    pinned.keys (by omega)
  have allocation := pinned.allocation
  have owner := pinned.owner
  have registry := pinned.registry
  have owners := pinned.owners
  simp only [typeName] at registered
  simp only [typeName, handleType, termType] at allocation owner registry owners
  simp [Result.handle, decode, registered, termOwner, termEntryOwner, clone, lookup, payload,
    allocation, owner, registry, owners, anyFresh, NativeCodec.roundtrip,
    referenceLimit, typeName, handleType, termType, a, b, c, d, e, f,
    Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f]

set_option maxHeartbeats 800000 in
/-- Decoding a live VM term temporarily acquires a Rust owner. Reading and
releasing it preserves the VM pin and contents, including across NIF calls. -/
theorem decode_read_release_handled_next {α β γ : Type} [NativeCodec α]
    (value : α) (finish : α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment) (id pin term : Nat)
    (ordered : id < pin ∧ pin < term ∧ term ≤ env.refCounter)
    (stored : env.nativeHeap = [
      (term, termType α, .tuple #[.reference id, .reference pin]),
      (pin, handleType α, .reference id),
      (id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (registered : typeName α ∈ env.nativeResourceTypes) :
    (do
      let owner ← decode (α := α) (.reference term)
      let result ← Result.handle (do
        let observed ← deref owner
        release owner
        finish observed) handler
      next result) env =
      ((Result.handle (finish value) handler) >>= next)
        {env with refCounter := env.refCounter + 1} := by
  have a : id ≠ pin := by omega
  have b : id ≠ term := by omega
  have c : pin ≠ term := by omega
  have d : env.refCounter + 1 ≠ id := by omega
  have e : env.refCounter + 1 ≠ pin := by omega
  have f : env.refCounter + 1 ≠ term := by omega
  simp only [typeName] at registered
  simp [decode, registered, termOwner, termEntryOwner, clone, release, deref, lookup, payload,
    Result.handle, stored, NativeCodec.roundtrip, referenceLimit, handleType,
    typeName, termType, a, b, c, d, Ne.symm a, Ne.symm b, Ne.symm c,
    Ne.symm d, Ne.symm e, Ne.symm f]

set_option maxHeartbeats 800000 in
/-- If a subsequent argument decoder fails, releasing the acquired Rust owner
before propagating badarg preserves the VM pin and resource contents. -/
theorem decode_failure_cleanup_handled_next {α β γ : Type} [NativeCodec α]
    (value : α) (handler : Exception → NativeM β) (next : β → NativeM γ)
    (env : Environment) (id pin term : Nat)
    (ordered : id < pin ∧ pin < term ∧ term ≤ env.refCounter)
    (stored : env.nativeHeap = [
      (term, termType α, .tuple #[.reference id, .reference pin]),
      (pin, handleType α, .reference id),
      (id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (registered : typeName α ∈ env.nativeResourceTypes) :
    ((Result.handle (do
      let owner ← decode (α := α) (.reference term)
      release owner
      Result.error (.error (.atom "badarg"))) handler) >>= next) env =
      (handler (.error (.atom "badarg")) >>= next)
        {env with refCounter := env.refCounter + 1} := by
  have a : id ≠ pin := by omega
  have b : id ≠ term := by omega
  have c : pin ≠ term := by omega
  have d : env.refCounter + 1 ≠ id := by omega
  have e : env.refCounter + 1 ≠ pin := by omega
  have f : env.refCounter + 1 ≠ term := by omega
  simp only [typeName] at registered
  simp [decode, registered, termOwner, termEntryOwner, clone, release, lookup, payload,
    Result.handle, stored, NativeCodec.roundtrip, referenceLimit, handleType,
    typeName, termType, a, b, c, d, Ne.symm a, Ne.symm b, Ne.symm c,
    Ne.symm d, Ne.symm e, Ne.symm f]

end NativeResourceArc
end Lynx

namespace Lynx

/-- A registered callback capability or the standard static no-op waker.
The identity is ignored for no-op wakers and is never a BEAM PID. -/
structure NativeWaker where
  id : Nat
  isNoop : Bool := false

/-- Only the borrowed waker identity is exposed by the supported Context operations. -/
structure NativeTaskContext where
  waker : NativeWaker

namespace NativeTaskContext

/-- Retain exactly the supplied borrowed waker; extension data is not observed. -/
@[expose] def fromWaker (waker : NativeWaker) : NativeTaskContext := ⟨waker⟩

end NativeTaskContext

namespace NativeWaker

/-- The standard static waker discards all wake requests without allocation. -/
@[expose] def noop : NativeWaker := ⟨0, true⟩

@[expose] def typeName : String := "rust:future:waker"

/-- Record a coalesced notification without changing the identity's other cells. -/
@[expose] def notifiedEnv (waker : NativeWaker) (env : Environment) : Environment :=
  if waker.isNoop then env else
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell}

/-- Notification requests may coalesce. No executor or implicit repoll is assumed. -/
@[expose] def pollWake (waker : NativeWaker) (env : Environment) :
    Option (Except Exception Unit × Environment) :=
  if waker.isNoop then some (.ok (), env) else
  let cells := env.nativeHeap.filter fun cell => cell.1 == waker.id
  if waker.id ≤ env.refCounter ∧ (cells == [(waker.id, typeName, .atom "idle")] ||
      cells == [(waker.id, typeName, .atom "notified")]) then
    some (.ok (), {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell})
  else some (.error .exhausted, env)

/-- A valid callback requests a wake atomically; invalid identities exhaust verification. -/
@[expose] def wakeByRef (waker : NativeWaker) : NativeM Unit :=
  if waker.isNoop then .ok () else
  .wait (pollWake waker) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- No-op callbacks do not allocate, notify or modify any environment field. -/
theorem wakeByRef_noop_next {α : Type} (next : Unit → NativeM α) (env : Environment) :
    (wakeByRef noop >>= next) env = next () env := by
  simp [wakeByRef, noop, NativeM.ok]

/-- Registered wake requests preserve all unrelated cells and every other runtime field. -/
theorem wakeByRef_registered (waker : NativeWaker) (env : Environment)
    (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "idle")])
    (registered : waker.isNoop = false) :
    wakeByRef waker env = (.ok (), {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell}) := by
  have ready : pollWake waker env = some (.ok (), {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell}) := by
    simp [pollWake, registered, stored, bounded]
  unfold wakeByRef
  simp only [registered, Bool.false_eq_true, ↓reduceIte]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- The wake request composes with the actual caller's continuation. -/
theorem wakeByRef_registered_next {α : Type} (waker : NativeWaker)
    (next : Unit → Result α) (env : Environment)
    (bounded : waker.id ≤ env.refCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "idle")])
    (registered : waker.isNoop = false) :
    (wakeByRef waker >>= next) env =
      next () {env with nativeHeap := env.nativeHeap.map fun cell =>
        if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell} := by
  have ready : pollWake waker env = some (.ok (), {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell}) := by
    simp [pollWake, registered, stored, bounded]
  unfold wakeByRef
  simp only [registered, Bool.false_eq_true, ↓reduceIte]
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- Requests coalesce in the logical notification cell. -/
theorem notifiedEnv_idempotent (waker : NativeWaker) (env : Environment) :
    notifiedEnv waker (notifiedEnv waker env) = notifiedEnv waker env := by
  cases mode : waker.isNoop <;> simp only [notifiedEnv, mode, Bool.false_eq_true,
    ↓reduceIte]
  · have maps : (env.nativeHeap.map (fun cell =>
        if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell)).map
        (fun cell => if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell) =
        env.nativeHeap.map (fun cell =>
          if cell.1 == waker.id then (waker.id, typeName, .atom "notified") else cell) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro cell _
      by_cases same : cell.1 = waker.id <;> simp [same]
    simp only [maps]

/-- A missing wake capability cannot complete a caller continuation. -/
theorem wakeByRef_missing_next {α : Type} (waker : NativeWaker)
    (next : Unit → Result α) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == waker.id) = [])
    (registered : waker.isNoop = false) :
    (wakeByRef waker >>= next) env = (.error .exhausted, env) := by
  have ready : pollWake waker env = some (.error .exhausted, env) := by
    simp [pollWake, registered, missing]
  unfold wakeByRef
  simp only [registered, Bool.false_eq_true, ↓reduceIte]
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- A task waits between polls; cancellation wins over a queued notification. -/
inductive Signal where
  | wake
  | cancel

/-- Atomically consume one coalesced wake or observe cancellation. An idle task
blocks. Invalid capabilities exhaust verification rather than becoming ready. -/
@[expose] def pollAwait (waker : NativeWaker) (cancelled : Environment → Bool)
    (env : Environment) : Option (Except Exception Signal × Environment) :=
  if waker.isNoop then
    if cancelled env then some (.ok .cancel, env) else none
  else match env.nativeHeap.filter (fun cell => cell.1 == waker.id) with
  | [(_, tag, .atom status)] =>
    if waker.id ≤ env.refCounter ∧ tag = typeName ∧ (status = "idle" ∨ status = "notified") then
      if cancelled env then some (.ok .cancel, env)
      else if status = "notified" then
        some (.ok .wake, {env with nativeHeap := env.nativeHeap.map fun cell =>
          if cell.1 == waker.id then (waker.id, typeName, .atom "idle") else cell})
      else none
    else some (.error .exhausted, env)
  | _ => some (.error .exhausted, env)

@[expose] def await (waker : NativeWaker) (cancelled : Environment → Bool) : NativeM Signal :=
  .wait (pollAwait waker cancelled) fun reply => match reply with
    | .ok signal => .ok signal
    | .error exception => .error exception

/-- A discarded wake never makes a no-op task runnable. Cancellation is separate. -/
theorem pollAwait_noop (cancelled : Environment → Bool) (env : Environment) :
    pollAwait noop cancelled env = if cancelled env then some (.ok .cancel, env) else none := rfl

theorem await_notified_next {α : Type} (waker : NativeWaker)
    (cancelled : Environment → Bool) (next : Signal → NativeM α) (env : Environment)
    (bounded : waker.id ≤ env.refCounter) (active : cancelled env = false)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "notified")])
    (registered : waker.isNoop = false) :
    (await waker cancelled >>= next) env = next .wake {env with
      nativeHeap := env.nativeHeap.map fun cell =>
        if cell.1 == waker.id then (waker.id, typeName, .atom "idle") else cell} := by
  have ready : pollAwait waker cancelled env = some (.ok .wake, {env with
      nativeHeap := env.nativeHeap.map fun cell =>
        if cell.1 == waker.id then (waker.id, typeName, .atom "idle") else cell}) := by
    simp [pollAwait, registered, bounded, stored, active]
  unfold await
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

theorem await_cancelled_next {α : Type} (waker : NativeWaker)
    (cancelled : Environment → Bool) (next : Signal → NativeM α) (env : Environment)
    (bounded : waker.id ≤ env.refCounter) (requested : cancelled env = true)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "notified")])
    (registered : waker.isNoop = false) :
    (await waker cancelled >>= next) env = next .cancel env := by
  have ready : pollAwait waker cancelled env = some (.ok .cancel, env) := by
    simp [pollAwait, registered, bounded, stored, requested]
  unfold await
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

theorem pollAwait_idle (waker : NativeWaker) (cancelled : Environment → Bool)
    (env : Environment) (bounded : waker.id ≤ env.refCounter) (active : cancelled env = false)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "idle")])
    (registered : waker.isNoop = false) :
    pollAwait waker cancelled env = none := by
  simp [pollAwait, registered, bounded, stored, active]

theorem await_cancelled_idle_next {α : Type} (waker : NativeWaker)
    (cancelled : Environment → Bool) (next : Signal → NativeM α) (env : Environment)
    (bounded : waker.id ≤ env.refCounter) (requested : cancelled env = true)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "idle")])
    (registered : waker.isNoop = false) :
    (await waker cancelled >>= next) env = next .cancel env := by
  have ready : pollAwait waker cancelled env = some (.ok .cancel, env) := by
    simp [pollAwait, registered, bounded, stored, requested]
  unfold await
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp

theorem pollAwait_missing (waker : NativeWaker) (cancelled : Environment → Bool)
    (env : Environment) (missing : env.nativeHeap.filter (fun cell => cell.1 == waker.id) = [])
    (registered : waker.isNoop = false) :
    pollAwait waker cancelled env = some (.error .exhausted, env) := by
  simp [pollAwait, registered, missing]

end NativeWaker

/- Logical task execution invokes a concrete extracted poll and destructor.
Physical executor dispatch, cancellation delivery and native callbacks are models. -/
namespace NativeTask

inductive Step (α σ : Type) where
  | pending : σ → NativeTaskContext → Step α σ
  | ready : α → σ → Step α σ

/-- Poll only after a notification, destroy on completion or between-poll
cancellation, and distinguish cancellation from a returned value. Fuel exhaustion
is a verification cutoff, never successful completion or implicit destruction. -/
@[expose] def drive {α σ : Type} (poll : σ → NativeTaskContext → NativeM (Step α σ))
    (destroy : σ → NativeM Unit) (cancelled : Environment → Bool)
    (context : NativeTaskContext) : Nat → σ → NativeM (Option α)
  | 0, _ => .error .exhausted
  | fuel + 1, state => do
    match ← poll state context with
    | .ready value finished =>
      destroy finished
      .ok (some value)
    | .pending retained updatedContext =>
      match ← NativeWaker.await updatedContext.waker cancelled with
      | .wake => drive poll destroy cancelled updatedContext fuel retained
      | .cancel =>
        destroy retained
        .ok none

end NativeTask
end Lynx

namespace Lynx

/-- Registered regular-file description; its position and bytes live in the shared heap.
Separate descriptors of the same physical file are outside this initial model. -/
structure NativeFile where
  id : Nat

/-- Opaque I/O error identity. No error payload, kind or destructor is modeled. -/
structure NativeIoError where
  identity : Nat

namespace NativeFile

@[expose] def typeName : String := "rust:regular-file"
@[expose] def limit : Nat := 1048576

/-- The script is an explicit choice of OS outcomes, not a verified OS implementation.
Visible writes may persist in any bytewise old/new combination before sync. -/
structure State where
  visible : ByteArray
  durable : ByteArray
  position : Nat
  script : Term

@[expose] def encode (state : State) : Term :=
  .tuple #[.bitstring state.visible 0, .bitstring state.durable 0,
    .integer state.position, state.script]

@[expose] def decode : Term → Option State
  | .tuple fields => do
    if size : fields.size = 4 then do
      let .bitstring visible bits _ := fields[0]'(by omega) | none
      let .bitstring durable durableBits _ := fields[1]'(by omega) | none
      let .integer position := fields[2]'(by omega) | none
      if bits != 0 || durableBits != 0 || position < 0 || visible.size > limit ||
          durable.size > visible.size || position.toNat > limit then none
      else some ⟨visible, durable, position.toNat, fields[3]'(by omega)⟩
    else none
  | _ => none

/-- A mask selects each byte from the previous persistent image or current visible
image. Length may advance but cannot shrink without a modeled truncate operation.
This assumes bytewise old/new tearing, with no device corruption or namespace loss. -/
@[expose] def persist (old visible mask : ByteArray) : Option ByteArray :=
  if old.size ≤ mask.size ∧ mask.size ≤ visible.size ∧
      mask.data.toList.all (fun byte => byte == 0 || byte == 1) then
    some ⟨mask.data.mapIdx fun index choice =>
      if choice == 1 then visible[index]! else old[index]!⟩
  else none

@[expose] def bytes (data : Slice U8) : ByteArray :=
  ⟨data.val.toArray.map fun byte => UInt8.ofNat byte.val⟩

/-- Extend gaps with zeroes and overwrite exactly the accepted input prefix. -/
@[expose] def overwrite (old : ByteArray) (position : Nat) (data : ByteArray) (count : Nat) : ByteArray :=
  if count = 0 then old else
  ⟨(old.data.toList.take position ++ List.replicate (position - old.size) 0 ++
    data.data.toList.take count ++ old.data.toList.drop (position + count)).toArray⟩

/-- Parse one operation outcome; malformed or absent choices exhaust verification. -/
@[expose] def action (operation : String) : Term → Option (Bool × Nat × ByteArray × Term)
  | .cons (.tuple fields) rest => do
    if size : fields.size = 4 then do
      let .atom kind := fields[0]'(by omega) | none
      let .atom status := fields[1]'(by omega) | none
      let .integer value := fields[2]'(by omega) | none
      let .bitstring mask bits _ := fields[3]'(by omega) | none
      if kind != operation || (status != "ok" && status != "error") || value < 0 || bits != 0 then none
      else some (status == "ok", value.toNat, mask, rest)
    else none
  | _ => none

@[expose] def writeStep (state : State) (data : Slice U8) :
    Option (core.result.Result Usize NativeIoError × State) := do
  if data.val.length > limit then none else do
  let (success, value, mask, rest) ← action "write" state.script
  if success then
    if bounded : value ≤ data.val.length then do
      if data.val.length > limit || state.position + value > limit then none else do
      let visible := overwrite state.visible state.position (bytes data) value
      let durable ← persist state.durable visible mask
      let count := Usize.ofNatCore value (by have := data.property; scalar_tac)
      some (.Ok count, ⟨visible, durable, state.position + value, rest⟩)
    else none
  else do
    let durable ← persist state.durable state.visible mask
    some (.Err ⟨value⟩, {state with durable := durable, script := rest})

/-- Replace only the returned prefix of a mutable byte slice. Its remaining
initialized bytes survive a short read. -/
@[expose] def readBuffer (state : State) (buffer : Slice U8) (count : Nat)
    (bounded : count ≤ buffer.val.length)
    (available : count ≤ state.visible.size - state.position) : Slice U8 :=
  .from ((state.visible.data.toList.drop state.position |>.take count |>.map
      fun byte => U8.ofNatCore byte.toNat (by have := byte.toNat_lt; scalar_tac)) ++
    buffer.val.drop count) (by
      have length : (state.visible.data.toList.drop state.position |>.take count).length = count := by
        simp only [List.length_take, List.length_drop, Array.length_toList]
        simp only [← ByteArray.size_data] at available
        omega
      have valid := buffer.property
      simp only [List.length_append, List.length_map, List.length_drop, length]
      omega)

/-- A regular-file read may return a short prefix or EOF. Explicit error choices
leave the initialized buffer and offset unchanged. Persistence may advance in
both cases independently of the read. -/
@[expose] def readStep (state : State) (buffer : Slice U8) :
    Option (core.result.Result Usize NativeIoError × State × Slice U8) := do
  if buffer.val.length > limit then none else do
  let (success, value, mask, rest) ← action "read" state.script
  let durable ← persist state.durable state.visible mask
  if success then
    if bounded : value ≤ buffer.val.length then
      if available : value ≤ state.visible.size - state.position then
        if value = 0 ∧ buffer.val.length > 0 ∧ state.position < state.visible.size then none
        else do
          let count := Usize.ofNatCore value (by have := buffer.property; scalar_tac)
          some (.Ok count, { state with
            position := state.position + value
            durable := durable
            script := rest }, readBuffer state buffer value bounded available)
      else none
    else none
  else some (.Err ⟨value⟩, {state with durable := durable, script := rest}, buffer)

/-- The constructor conversion is generated from the actual extracted SeekFrom
schema; integer widths are retained in the runtime argument. -/
inductive SeekFrom where
  | start : U64 → SeekFrom
  | end_ : I64 → SeekFrom
  | current : I64 → SeekFrom

@[expose] def seekTarget (state : State) : SeekFrom → Int
  | .start offset => offset.val
  | .end_ offset => (state.visible.size : Int) + offset.val
  | .current offset => (state.position : Int) + offset.val

/-- Seeking changes no visible bytes or length, including beyond EOF. Negative
successes and positions beyond the configured bound are invalid model choices.
Failure preserves the previous offset under the explicit std/OS model. -/
@[expose] def seekStep (state : State) (origin : SeekFrom) :
    Option (core.result.Result U64 NativeIoError × State) := do
  let (success, value, mask, rest) ← action "seek" state.script
  let durable ← persist state.durable state.visible mask
  if success then
    let target := seekTarget state origin
    if outside : target < 0 ∨ target.toNat > limit ∨ value != 0 then none else
      let offset := U64.ofNatCore target.toNat (by
        have : target.toNat ≤ limit := by omega
        simp only [limit] at this
        scalar_tac)
      some (.Ok offset, { state with
        position := target.toNat
        durable := durable
        script := rest })
  else some (.Err ⟨value⟩, {state with durable := durable, script := rest})

@[expose] def syncStep (state : State) :
    Option (core.result.Result Unit NativeIoError × State) := do
  let (success, value, mask, rest) ← action "sync_all" state.script
  if success then
    if value != 0 then none
    else some (.Ok (), {state with durable := state.visible, script := rest})
  else do
    let durable ← persist state.durable state.visible mask
    some (.Err ⟨value⟩, {state with durable := durable, script := rest})

@[expose] def lookup (file : NativeFile) (env : Environment) : Option State :=
  if file.id ≤ env.refCounter then
    match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
    | [(_, tag, contents)] => if tag == typeName then decode contents else none
    | _ => none
  else none

@[expose] def store (file : NativeFile) (state : State) (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == file.id then (file.id, typeName, encode state) else cell}

@[expose] def blocked (state : State) : Bool :=
  match state.script with | .cons (.atom "blocked") _ => true | _ => false

/-- One atomic regular-file write, including partial results, errors and blocking.
Write completion does not assert persistence. Invalid capabilities/choices cut off. -/
@[expose] def pollWrite (file : NativeFile) (data : Slice U8) (env : Environment) :
    Option (Except Exception (core.result.Result Usize NativeIoError × NativeFile) × Environment) :=
  match lookup file env with
  | none => some (.error .exhausted, env)
  | some state =>
    if blocked state then none else
    match writeStep state data with
    | none => some (.error .exhausted, env)
    | some (reply, updated) => some (.ok (reply, file), store file updated env)

@[expose] def write (file : NativeFile) (data : Slice U8) :
    NativeM (core.result.Result Usize NativeIoError × NativeFile) :=
  .wait (pollWrite file data) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

@[expose] def pollRead (file : NativeFile) (buffer : Slice U8) (env : Environment) :
    Option (Except Exception (core.result.Result Usize NativeIoError × NativeFile × Slice U8) × Environment) :=
  match lookup file env with
  | none => some (.error .exhausted, env)
  | some state =>
    if blocked state then none else
    match readStep state buffer with
    | none => some (.error .exhausted, env)
    | some (reply, updated, buffer) => some (.ok (reply, file, buffer), store file updated env)

@[expose] def read (file : NativeFile) (buffer : Slice U8) :
    NativeM (core.result.Result Usize NativeIoError × NativeFile × Slice U8) :=
  .wait (pollRead file buffer) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

@[expose] def pollSeek (file : NativeFile) (origin : SeekFrom) (env : Environment) :
    Option (Except Exception (core.result.Result U64 NativeIoError × NativeFile) × Environment) :=
  match lookup file env with
  | none => some (.error .exhausted, env)
  | some state =>
    if blocked state then none else
    match seekStep state origin with
    | none => some (.error .exhausted, env)
    | some (reply, updated) => some (.ok (reply, file), store file updated env)

@[expose] def seek (file : NativeFile) (origin : SeekFrom) :
    NativeM (core.result.Result U64 NativeIoError × NativeFile) :=
  .wait (pollSeek file origin) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- Synchronization errors may still persist a torn image; only success guarantees
all visible file contents and length. Directory/device correspondence is assumed. -/
@[expose] def pollSync (file : NativeFile) (env : Environment) :
    Option (Except Exception (core.result.Result Unit NativeIoError) × Environment) :=
  match lookup file env with
  | none => some (.error .exhausted, env)
  | some state =>
    if blocked state then none else
    match syncStep state with
    | none => some (.error .exhausted, env)
    | some (reply, updated) => some (.ok reply, store file updated env)

@[expose] def syncAll (file : NativeFile) : NativeM (core.result.Result Unit NativeIoError) :=
  .wait (pollSync file) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- A single independent file's possible persistent image after power loss.
The high-water mark is ghost freshness bookkeeping, not on-disk application data.
Native opening and namespace correspondence are separate trusted boundaries. -/
structure Image where
  bytes : ByteArray
  highWater : Nat

/-- Permit any additional persistence allowed by the file model before power
loss, including torn unsynchronized writes. No volatile process state is saved. -/
@[expose] def crashImage (file : NativeFile) (mask : ByteArray) (env : Environment) : Option Image := do
  let state ← lookup file env
  let durable ← persist state.durable state.visible mask
  some ⟨durable, env.refCounter⟩

/-- Admit one newly opened, independent file into a fresh machine. This is an
explicit host/OS boundary, not a verified implementation of std::fs::File::open.
Old capabilities and all previous process/resource/lock state are discarded. -/
@[expose] def restart (image : Image) (script : Term) : Option (NativeFile × Environment) :=
  if image.bytes.size > limit then none else
    let file : NativeFile := ⟨image.highWater + 1⟩
    some (file, {
      refCounter := file.id
      nativeHeap := [(file.id, typeName, encode ⟨image.bytes, image.bytes, 0, script⟩)] })

end NativeFile
end Lynx
