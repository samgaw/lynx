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
Guard unwind, resource lifetimes, native executors and FFI execution require
separate models. -/

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
payload to scalar types, so there is no user destructor to execute. -/
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

/-- Creating then consuming an owned scalar-compatible mutex reclaims its cell
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

end Lynx.NativeGuard
