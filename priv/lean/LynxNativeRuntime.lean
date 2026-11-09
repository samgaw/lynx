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

attribute [cbv_eval] U64.max_eq

@[cbv_eval] theorem u64Bv_eq (value : U64) : U64.bv value = UScalar.bv value := rfl

/-- Evaluate checked addition using Aeneas's proved bit-vector specification.
Overflow remains `none`; this equation does not replace Rust arithmetic. -/
@[cbv_eval] theorem checkedAddU64_eq (x y : U64) :
    U64.checked_add x y =
      if x.val + y.val ≤ U64.max then some (⟨x.bv + y.bv⟩ : U64) else none := by
  have specification := U64.checked_add_bv_spec x y
  cases result : U64.checked_add x y with
  | none =>
    simp only [result] at specification
    simp only [if_neg (Nat.not_le_of_lt specification)]
  | some value =>
    simp only [result] at specification
    rw [if_pos specification.1]
    congr 1
    cases value
    congr 1
    exact specification.2.2

@[expose] def ok {α : Type} (value : α) : NativeM α := Result.ok value

@[expose] def fail {α : Type} (error : Error) : NativeM α :=
  match error with
  | .panic => .error (.error (.atom "rust_panicked"))
  | .undef => .error .exhausted

@[expose] def lift {α : Type} (value : α) : NativeM α := Result.ok value

/-- A successful standard `Result::expect` transfers the actual Ok payload.
The error path cannot establish a Rust outcome: Debug formatting, error
destruction and unwind require separate models before that path is supported. -/
@[expose] def expectOk {T E : Type} (value : core.result.Result T E) (_message : Str) : NativeM T :=
  match value with
  | .Ok value => .ok value
  | .Err _ => .error .exhausted

@[simp] theorem expectOk_ok {T E : Type} (value : T) (message : Str) :
    expectOk (.Ok value : core.result.Result T E) message = .ok value := rfl

@[simp] theorem expectOk_error {T E : Type} (error : E) (message : Str) :
    expectOk (.Err error : core.result.Result T E) message = .error .exhausted := rfl

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

/-- Avoid evaluating a linear natural-number comparison while constructing the
range witness. This is the same unsigned heap decoder, including rejected inputs. -/
@[cbv_eval] theorem decode_unsigned_eq {ty : UScalarTy} (term : Term) :
    decode (α := UScalar ty) term =
      match term with
      | .integer value => if 0 ≤ value ∧ value < (2 ^ ty.numBits : Int) then
          some (⟨BitVec.ofNat ty.numBits value.toNat⟩ : UScalar ty) else none
      | _ => none := by
  cases term <;> simp only [decode]
  rename_i value
  by_cases nonnegative : 0 ≤ value
  · have range : value.toNat < 2 ^ ty.numBits ↔ value < (2 ^ ty.numBits : Int) := by
      rw [← Int.ofNat_lt, Int.toNat_of_nonneg nonnegative, Int.natCast_pow]
      rfl
    simp only [nonnegative, true_and, ← range]
    split
    · congr 1
      simp [UScalar.ofNatCore, BitVec.ofFin_eq_ofNat]
    · rfl
  · simp [nonnegative]

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

/-- Allocate a logical cell in one atomic scheduler transition. Freshness and
publication cannot race with another logical allocation. Physical allocation
and the native primitive's implementation remain explicit trusted boundaries. -/
@[expose] def allocate (typeName : String) (value : Term) : NativeM Nat :=
  .wait (fun env => some (
    let id := env.nativeRefCounter + 1
    if env.nativeHeap.any (fun cell => cell.1 == id) then
      ((Except.error .exhausted : Except Exception Nat), env)
    else (Except.ok id, { env with
      nativeRefCounter := id, nativeHeap := (id, typeName, value) :: env.nativeHeap })))
    Result.ofExcept

/-- Wrong-type, missing and ambiguous identities exhaust verification. This
helper is not a Rustler resource decoder or an Elixir-visible failure. -/
@[expose] def readCell (typeName : String) (id : Nat) : NativeM Term :=
  .nativeGet fun env =>
    match env.nativeHeap.filter (fun cell => cell.1 == id) with
    | [(_, storedType, value)] =>
      if storedType == typeName then .ok value else .error .exhausted
    | _ => .error .exhausted

@[simp] theorem allocate_run (typeName : String) (value : Term) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    allocate typeName value env =
      (.ok (env.nativeRefCounter + 1), { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := (env.nativeRefCounter + 1, typeName, value) :: env.nativeHeap }) := by
  simp [allocate, fresh]

@[simp] theorem readCell_run (typeName : String) (id : Nat) (value : Term) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == id) = [(id, typeName, value)]) :
    readCell typeName id env = (.ok value, env) := by
  simp [readCell, stored]

/-- Consume a unique typed cell in one atomic transition. Concurrent creation
or cleanup of unrelated cells cannot be overwritten. The caller must establish
the destructor's payload/ownership requirements; malformed identities exhaust
verification without changing state. -/
@[expose] def removeCell (typeName : String) (id : Nat) : NativeM Term :=
  .wait (fun env => some (
    match env.nativeHeap.filter (fun cell => cell.1 == id) with
    | [(_, storedType, value)] =>
      if storedType == typeName then
        (Except.ok value, { env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != id) })
      else ((Except.error .exhausted : Except Exception Term), env)
    | _ => (Except.error .exhausted, env))) Result.ofExcept

end NativeM

/-- Movable logical mutex identity. Mutable payloads live in the shared heap. -/
structure NativeMutex (α : Type) where
  id : Nat

namespace NativeMutex

@[expose] def typeName (α : Type) [NativeCodec α] : String :=
  "std::sync::Mutex<" ++ NativeCodec.typeName (α := α) ++ ">"

instance {α : Type} [NativeCodec α] : NativeCodec (NativeMutex α) where
  typeName := NativeMutex.typeName α
  encode mutex := .nativeReference mutex.id
  decode
    | .nativeReference id => some ⟨id⟩
    | _ => none
  decode_encode mutex := by cases mutex; rfl

/-- Model only the initialization of a fresh unlocked, unpoisoned mutex. -/
@[expose] def new {α : Type} [NativeCodec α] (value : α) : NativeM (NativeMutex α) := do
  let id ← NativeM.allocate (typeName α)
    (.tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])
  return { id }

@[simp] theorem new_run {α : Type} [NativeCodec α] (value : α) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    new value env =
      (.ok ⟨env.nativeRefCounter + 1⟩, { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := (env.nativeRefCounter + 1, typeName α,
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
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    ((do let mutex ← new value; dispose mutex; next) : NativeM β) env =
      next { env with nativeRefCounter := env.nativeRefCounter + 1 } := by
  have absent : env.nativeHeap.filter (fun cell => cell.1 == env.nativeRefCounter + 1) = [] := by
    simpa only [List.filter_eq_nil_iff, List.any_eq_false] using fresh
  have kept : env.nativeHeap.filter (fun cell => cell.1 != env.nativeRefCounter + 1) = env.nativeHeap := by
    apply List.filter_eq_self.mpr
    intro cell member
    have unused := (List.any_eq_false.mp fresh) cell member
    simpa using unused
  simp [new, NativeM.allocate, dispose, NativeM.readCell, NativeM.removeCell,
    fresh, absent, kept, NativeCodec.roundtrip]

theorem new_dispose {α : Type} [NativeCodec α] (value : α) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    ((new value >>= dispose) : NativeM Unit) env =
      (.ok (), { env with nativeRefCounter := env.nativeRefCounter + 1 }) := by
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
                let token := env.nativeRefCounter + 1
                if env.nativeHeap.any (fun cell => cell.1 == token) then invalid else
                let guard : NativeGuard α := ⟨mutex, token, env.currentPid, value⟩
                let contents := .tuple #[.tuple #[.atom "locked", .pid env.currentPid, .nativeReference token],
                  poisonState, payload]
                let updated := { env with nativeRefCounter := token, nativeHeap := env.nativeHeap.map fun cell =>
                  if cell.1 == mutex.id then (mutex.id, typeName α, contents) else cell }
                some (.ok (if poison == "poisoned" then .Err ⟨guard⟩ else .Ok guard), updated)
              | .tuple owner =>
                if ownerSize : owner.size = 3 then
                  let marker := owner[0]'(by omega)
                  let context := owner[1]'(by omega)
                  let token := owner[2]'(by omega)
                  match marker, context, token with
                  | .atom "locked", .pid current, .nativeReference _ =>
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
  .tuple #[.tuple #[.atom "locked", .pid context, .nativeReference token],
    .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value]

/-- Acquisition preserves unrelated cells and returns ownership even when poisoned. -/
theorem pollLock_unlocked {α : Type} [NativeCodec α] (mutex : NativeMutex α)
    (value : α) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, typeName α, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    pollLock mutex env = some (.ok (
      if poisoned then .Err ⟨⟨mutex, env.nativeRefCounter + 1, env.currentPid, value⟩⟩
      else .Ok ⟨mutex, env.nativeRefCounter + 1, env.currentPid, value⟩),
      { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, typeName α, lockedContents env.currentPid (env.nativeRefCounter + 1) poisoned value)
          else cell }) := by
  cases poisoned <;> simp [pollLock, stored, fresh, NativeCodec.roundtrip, lockedContents]

/-- In a standalone computation a ready acquisition returns its owned guard. -/
theorem lock_unlocked {α : Type} [NativeCodec α] (mutex : NativeMutex α)
    (value : α) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, typeName α, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    lock mutex env = (.ok (
      if poisoned then .Err ⟨⟨mutex, env.nativeRefCounter + 1, env.currentPid, value⟩⟩
      else .Ok ⟨mutex, env.nativeRefCounter + 1, env.currentPid, value⟩),
      { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
          (mutex.id, typeName α, lockedContents env.currentPid (env.nativeRefCounter + 1) poisoned value)
          else cell }) := by
  unfold lock
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ (pollLock_unlocked mutex value poisoned env stored fresh)]
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
            | .atom "locked", .pid owner, .nativeReference token =>
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
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
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
  rw [Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
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
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
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
  /-- False only for compiler-certified cleanup with no observable effects. -/
  observable : Bool := true

/-- Result of an explicit native finalizer callback dispatch. Busy work has not
completed and must never be treated as a successful cleanup. -/
inductive NativeFinalizerStatus where
  | idle
  | busy
  | completed

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

/-- Validate a live ownership token, its typed allocation and the complete owner
count. This exposes model validation for implementation-linked client proofs. -/
@[expose] def ownership {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment) : Option (Nat × α) := do
  let [(_, actualHandleType, .nativeReference target)] :=
    env.nativeHeap.filter (fun cell => cell.1 == handle.token) | none
  if actualHandleType != handleType α || target != handle.id then none else
  let [(_, actualType, contents)] :=
    env.nativeHeap.filter (fun cell => cell.1 == handle.id) | none
  if actualType != typeName α then none else
  let (count, value) ← (do
    let .tuple fields := contents | none
    if size : fields.size = 2 then
      let .integer count := (fields[0]'(by omega)) | none
      if 0 < count ∧ count ≤ referenceLimit then
        let value ← NativeCodec.decode (fields[1]'(by omega))
        some (count.toNat, value)
      else none
    else none)
  let tokens := env.nativeHeap.filter fun cell =>
    cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id
  if tokens.length = count then some (count, value) else none

/-- Allocation requires modeled registration, as ResourceArc::new unwraps the
registered type. Physical allocation success is an explicit FFI boundary. -/
@[expose] def new {α : Type} [NativeCodec α] (value : α) : NativeM (NativeResourceArc α) :=
  .nativeGet fun env =>
    if typeName α ∈ env.nativeResourceTypes then do
      let id ← NativeM.allocate (typeName α) (.tuple #[.integer 1, NativeCodec.encode value])
      let token ← NativeM.allocate (handleType α) (.nativeReference id)
      .ok ⟨id, token⟩
    else NativeM.fail .panic

/-- Retaining a handle allocates a distinct ownership token for the same cell. -/
@[expose] def clone {α : Type} [NativeCodec α] (handle : NativeResourceArc α) :
    NativeM (NativeResourceArc α) :=
  .nativeModify (fun env =>
    match ownership handle env with
    | some (count, value) =>
      let token := env.nativeRefCounter + 1
      if count < referenceLimit && !(env.nativeHeap.any (fun cell => cell.1 == token)) then
        (Except.ok ⟨handle.id, token⟩, { env with nativeRefCounter := token, nativeHeap :=
          (token, handleType α, .nativeReference handle.id) :: env.nativeHeap.map fun cell =>
            if cell.1 == handle.id then
              (handle.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value])
            else cell })
      else ((Except.error .exhausted : Except Exception (NativeResourceArc α)), env)
    | none => (Except.error .exhausted, env)) Result.ofExcept

/-- A shared immutable borrow observes the allocation through its live token. -/
@[expose] def deref {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM α :=
  .nativeGet fun env =>
    match ownership handle env with
    | some (_, value) => .ok value
    | none => .error .exhausted

/-- The framed environment after final-owner retirement. This projection is
for cleanup contracts; takeOwner validates that final retirement is permitted. -/
@[expose] def retiredState {α : Type} (handle : NativeResourceArc α) (env : Environment) : Environment :=
  {env with nativeHeap :=
    (env.nativeHeap.filter (fun cell => cell.1 != handle.token)).filter (fun cell => cell.1 != handle.id)}

/-- Atomically consume a validated owner and update its allocation's count.
Only the final owner receives the payload, transferring its cleanup obligation.
After retirement no token can re-enter that allocation. -/
@[expose] def ownerState {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment) : Except Exception (Option α) × Environment :=
    match ownership handle env with
    | some (count, value) =>
      let remaining := env.nativeHeap.filter (fun cell => cell.1 != handle.token)
      let heap := if count = 1 then (retiredState handle env).nativeHeap
        else remaining.map fun cell => if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer (count - 1), NativeCodec.encode value]) else cell
      (Except.ok (if count = 1 then some value else none), {env with nativeHeap := heap})
    | none => ((Except.error .exhausted : Except Exception (Option α)), env)

@[expose] def takeOwner {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM (Option α) :=
  .nativeModify (ownerState handle) Result.ofExcept

@[expose] def finalizerType (α : Type) [NativeCodec α] : String :=
  "resource-finalizer<" ++ NativeCodec.typeName (α := α) ++ ">"

@[expose] def runningFinalizerType (α : Type) [NativeCodec α] : String :=
  "resource-finalizer-running<" ++ NativeCodec.typeName (α := α) ++ ">"

/-- Select an explicit callback policy when the final owner has observable
cleanup. Missing policy exhausts verification without changing ownership. -/
@[expose] def ownedState {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (env : Environment) : Except Exception (Option α) × Environment :=
  match ownerState handle env with
  | (.ok none, updated) => (.ok none, updated)
  | (.ok (some value), updated) =>
    if !NativeResourceCleanup.observable (α := α) then (.ok (some value), updated) else
    match env.nativeFinalizerMode with
    | .unspecified => (.error .exhausted, env)
    | .synchronous => (.ok (some value), updated)
    | .deferred => (.ok none, {updated with nativeHeap :=
        (handle.id, finalizerType α, NativeCodec.encode value) :: updated.nativeHeap})
  | (.error error, _) => (.error error, env)

/-- Consume exactly this Rust ownership token. Admission requires a payload with
no Rust destructor and default resource callbacks. A VM pin is a separate token
and survives release of every Rust-owned handle. -/
@[expose] def release {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM Unit := do
  let _ ← takeOwner handle
  Result.ok ()

instance {α : Type} [NativeCodec α] : NativeDrop (NativeResourceArc α) where
  drop := release

/-- Registration failure unwinds the still-owned argument before reporting panic.
Physical allocation success and the VM callback remain explicit FFI boundaries. -/
@[expose] def newOwned {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (value : α) : NativeM (NativeResourceArc α) :=
  .nativeGet fun env =>
    if typeName α ∈ env.nativeResourceTypes then new value
    else do
      NativeResourceCleanup.cleanup value
      NativeM.fail .panic

/-- Retirement and callback-policy selection are atomic. Synchronous cleanup
requires explicit admission; deferred cleanup is queued separately from the
Rust call's return. OTP does not guarantee callback completion on release. -/
@[expose] def releaseOwned {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) : NativeM Unit := do
  let final ← Result.nativeModify (ownedState handle) Result.ofExcept
  match final with
  | none => Result.ok ()
  | some value => NativeResourceCleanup.cleanup value

/-- Claim pending work once. Running callbacks are observable as busy rather
than complete. Dispatch is an explicit environment action, not a BEAM process
spawn or a proof of the VM's callback scheduler. -/
@[expose] def runFinalizer {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (identity : Nat) : NativeM NativeFinalizerStatus := do
  let claim ← Result.nativeModify (fun env =>
    match env.nativeHeap.filter (fun cell => cell.1 == identity) with
    | [] => (Except.ok (.inl NativeFinalizerStatus.idle : Sum NativeFinalizerStatus α), env)
    | [(_, tag, payload)] =>
      if tag == runningFinalizerType α then (.ok (.inl .busy), env) else
      if tag == finalizerType α then
        match NativeCodec.decode payload with
        | none => (.error .exhausted, env)
        | some value => (.ok (.inr value), {env with nativeHeap := env.nativeHeap.map fun cell =>
            if cell.1 == identity then (identity, runningFinalizerType α, .atom "running") else cell})
      else (.error .exhausted, env)
    | _ => (.error .exhausted, env)) Result.ofExcept
  match claim with
  | .inl status => Result.ok status
  | .inr value =>
    NativeResourceCleanup.cleanup value
    let _ ← NativeM.removeCell (runningFinalizerType α) identity
    Result.ok .completed

instance {α : Type} [NativeCodec α] [NativeResourceCleanup α] :
    NativeOwnedDrop (NativeResourceArc α) where
  drop := releaseOwned

/-- A validated final token retires the Arc before running its payload cleanup. -/
theorem releaseOwned_last_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env : Environment)
    (policy : NativeResourceCleanup.observable (α := α) = false ∨ env.nativeFinalizerMode = .synchronous)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 1) :
    (releaseOwned handle >>= next) env =
      (do NativeResourceCleanup.cleanup value; next ()) (retiredState handle env) := by
  rcases policy with policy | policy
  all_goals
    simp [releaseOwned, takeOwner, ownerState, ownedState, retiredState, ownership, token, stored, owners,
    NativeCodec.roundtrip, referenceLimit, policy]

/-- Releasing one of two validated tokens does not run payload destruction. -/
theorem releaseOwned_retained_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 2) :
    (releaseOwned handle >>= next) env = (release handle >>= next) env := by
  simp [releaseOwned, release, takeOwner, ownerState, ownedState, retiredState, ownership, token, stored, owners,
    NativeCodec.roundtrip, referenceLimit]

/-- A live resource borrow retains its exact shared payload identity. -/
theorem deref_single_next {α β : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (next : α → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 1) :
    (deref handle >>= next) env = next value env := by
  simp [deref, ownership, token, stored, owners, NativeCodec.roundtrip, referenceLimit]

theorem deref_retained_handled_next {α β γ : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (finish : α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 2) :
    ((Result.handle (deref handle >>= finish) handler) >>= next) env =
      ((Result.handle (finish value) handler) >>= next) env := by
  simp [Result.handle, deref, ownership, token, stored, owners, NativeCodec.roundtrip, referenceLimit]

/-- Borrowing observes the shared payload for any validated number of owners,
including overlapping decoded NIF arguments. It consumes no ownership token. -/
theorem deref_live_prefix {α : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (count : Nat) (env : Environment)
    (positive : 0 < count) (bounded : count ≤ referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count) :
    Result.ReadyPrefix (deref handle) env (.ok value) env := by
  unfold deref
  apply Result.ReadyPrefix.nativeGet
  have boundedInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  simp [ownership, token, stored, owners, NativeCodec.roundtrip,
    positive, boundedInt]
  exact .refl _ _

/-- A resource borrow remains a real read inside a scheduled native trace. -/
theorem deref_live_sharedSteps {α β : Type} [NativeCodec α]
    (pid : PID) (handle : NativeResourceArc α) (value : α) (count : Nat)
    (before after : Nat × List (Nat × String × Term)) (finish : α → NativeM β) (answer : β)
    (positive : 0 < count) (bounded : count ≤ referenceLimit)
    (token : before.2.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : before.2.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count)
    (rest : Result.SharedSteps pid (finish value) before answer after) :
    Result.SharedSteps pid (deref handle >>= finish) before answer after := by
  unfold deref
  rw [Result.nativeGet_bind]
  refine .read _ (finish value) before after answer ?_ rest
  intro env _ _ heap
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  simp [ownership, heap, token, stored, owners, NativeCodec.roundtrip,
    positive, boundInt]

/-- Resource reads and owner consumption retain mutual exclusion at every local step. -/
theorem deref_live_exclusiveSteps {α β γ : Type} [NativeCodec α]
    (pid peer : PID) (peerPoll : Environment → Option (γ × Environment)) (handle : NativeResourceArc α) (value : α) (count : Nat)
    (before after : Nat × List (Nat × String × Term)) (finish : α → NativeM β) (answer : β)
    (positive : 0 < count) (bounded : count ≤ referenceLimit)
    (token : before.2.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : before.2.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count)
    (blocked : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
      env.nativeHeap = before.2 → peerPoll env = none)
    (rest : Result.ExclusiveSteps pid peer peerPoll (finish value) before answer after) :
    Result.ExclusiveSteps pid peer peerPoll (deref handle >>= finish) before answer after := by
  unfold deref
  rw [Result.nativeGet_bind]
  refine .read _ (finish value) before after answer ?_ blocked rest
  intro env _ _ heap
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  simp [ownership, heap, token, stored, owners, NativeCodec.roundtrip,
    positive, boundInt]

/-- Borrow locally and stop before the caller's next scheduler operation. -/
theorem deref_live_registeredPrefix {α : Type} [NativeCodec α]
    (pid : PID) (handle : NativeResourceArc α) (value : α) (count : Nat)
    (before : Nat × List (Nat × String × Term)) (types : List String)
    (positive : 0 < count) (bounded : count ≤ referenceLimit)
    (token : before.2.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : before.2.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count) :
    Result.RegisteredPrefix pid (deref handle) before types (.ok value) before types := by
  unfold deref
  refine .read _ (.ok value) before before types types _ ?_ (.refl _ _ _)
  intro env _ _ heap _
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  simp [ownership, heap, token, stored, owners, NativeCodec.roundtrip, positive, boundInt]

/-- A retained borrow is an actual state-read prefix and leaves ownership and
payload intact. This interface retains operation boundaries for crash proofs. -/
theorem deref_retained_prefix {α : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 2) :
    Result.ReadyPrefix (deref handle) env (.ok value) env := by
  exact deref_live_prefix handle value 2 env (by decide) (by decide) token stored owners

/-- Retaining a live allocation preserves its payload and every unrelated cell,
including while another Rust caller already owns a decoded token. -/
theorem clone_live_prefix {α : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (count : Nat) (env : Environment)
    (positive : 0 < count) (bounded : count < referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    Result.ReadyPrefix (clone handle) env
      (.ok (⟨handle.id, env.nativeRefCounter + 1⟩ : NativeResourceArc α)) {env with
        nativeRefCounter := env.nativeRefCounter + 1, nativeHeap :=
          (env.nativeRefCounter + 1, handleType α, .nativeReference handle.id) :: env.nativeHeap.map fun cell =>
            if cell.1 == handle.id then
              (handle.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value]) else cell} := by
  unfold clone
  let updated : Environment := {env with nativeRefCounter := env.nativeRefCounter + 1, nativeHeap :=
    (env.nativeRefCounter + 1, handleType α, .nativeReference handle.id) :: env.nativeHeap.map fun cell =>
      if cell.1 == handle.id then
        (handle.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value]) else cell}
  refine Result.ReadyPrefix.nativeModify _ _ (Except.ok ⟨handle.id,env.nativeRefCounter + 1⟩)
    env updated _ _ ?_ (.refl _ _)
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast Nat.le_of_lt bounded
  simp [ownership, token, stored, owners, NativeCodec.roundtrip, positive,
    boundInt, bounded, fresh, updated]

/-- Retaining a validated sole owner creates another token for the same value. -/
theorem clone_single_next {α β : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (next : NativeResourceArc α → NativeM β)
    (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 1)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    (clone handle >>= next) env = next ⟨handle.id, env.nativeRefCounter + 1⟩ {env with
      nativeRefCounter := env.nativeRefCounter + 1, nativeHeap :=
        (env.nativeRefCounter + 1, handleType α, .nativeReference handle.id) :: env.nativeHeap.map fun cell =>
          if cell.1 == handle.id then
            (handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value]) else cell } := by
  simp [clone, ownership, token, stored, owners, fresh,
    NativeCodec.roundtrip, referenceLimit]

/-- Consuming a nonfinal token preserves payload cells and the other owner. -/
theorem releaseOwned_retained_run_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 2) :
    (releaseOwned handle >>= next) env = next () {env with nativeHeap :=
      (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value]) else cell } := by
  rw [releaseOwned_retained_next handle value next env token stored owners]
  simp [release, takeOwner, ownerState, ownedState, retiredState, ownership, token, stored, owners, NativeCodec.roundtrip, referenceLimit]

/-- Nonfinal release supports overlapping Rust callers and a VM pin. The
complete owner registry must agree with the stored count before consumption. -/
theorem releaseOwned_live_prefix {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (count : Nat) (env : Environment)
    (nonfinal : 1 < count) (bounded : count ≤ referenceLimit)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count) :
    Result.ReadyPrefix (releaseOwned handle) env (.ok ()) {env with nativeHeap :=
      (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer (count - 1), NativeCodec.encode value]) else cell} := by
  have positive : 0 < count := by omega
  have different : count ≠ 1 := by omega
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  unfold releaseOwned ownedState ownerState
  rw [Result.nativeModify_bind]
  let updated : Environment := {env with nativeHeap :=
    (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
      if cell.1 == handle.id then
        (handle.id,typeName α,.tuple #[.integer (count - 1),NativeCodec.encode value]) else cell}
  refine Result.ReadyPrefix.nativeModify _ _ (Except.ok none) env updated _ _ ?_ (.refl _ _)
  simp [ownership, token, stored, owners, NativeCodec.roundtrip, positive, boundInt,
    different, updated]

/-- Nonfinal owner release retains its atomic retirement step in a scheduled
trace. The continuation receives the heap after consuming exactly this token. -/
theorem releaseOwned_live_sharedSteps {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (pid : PID) (handle : NativeResourceArc α) (value : α) (count : Nat)
    (before after : Nat × List (Nat × String × Term)) (finish : Unit → NativeM β) (answer : β)
    (nonfinal : 1 < count) (bounded : count ≤ referenceLimit)
    (token : before.2.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : before.2.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count)
    (rest : Result.SharedSteps pid (finish ())
      (before.1, (before.2.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer (count - 1), NativeCodec.encode value]) else cell)
      answer after) :
    Result.SharedSteps pid (releaseOwned handle >>= finish) before answer after := by
  have positive : 0 < count := by omega
  have different : count ≠ 1 := by omega
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  unfold releaseOwned ownedState ownerState
  simp only [Result.nativeModify_bind]
  refine .modify _ _ (Except.ok none) before _ after answer ?_ rest
  intro env _ counter heap
  simp [ownership, counter, heap, token, stored, owners, NativeCodec.roundtrip,
    positive, boundInt, different]

/-- Resource reads and owner consumption retain mutual exclusion at every local step. -/
theorem releaseOwned_live_exclusiveSteps {α β γ : Type} [NativeCodec α] [NativeResourceCleanup α]
    (pid peer : PID) (peerPoll : Environment → Option (γ × Environment)) (handle : NativeResourceArc α) (value : α) (count : Nat)
    (before after : Nat × List (Nat × String × Term)) (finish : Unit → NativeM β) (answer : β)
    (nonfinal : 1 < count) (bounded : count ≤ referenceLimit)
    (token : before.2.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : before.2.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = count)
    (blocked : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
      env.nativeHeap = before.2 → peerPoll env = none)
    (rest : Result.ExclusiveSteps pid peer peerPoll (finish ())
      (before.1, (before.2.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer (count - 1), NativeCodec.encode value]) else cell)
      answer after) :
    Result.ExclusiveSteps pid peer peerPoll (releaseOwned handle >>= finish) before answer after := by
  have positive : 0 < count := by omega
  have different : count ≠ 1 := by omega
  have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast bounded
  unfold releaseOwned ownedState ownerState
  simp only [Result.nativeModify_bind]
  refine .modify _ _ (Except.ok none) before _ after answer ?_ blocked rest
  intro env _ counter heap
  simp [ownership, counter, heap, token, stored, owners, NativeCodec.roundtrip,
    positive, boundInt, different]

/-- Consuming a retained Rust owner is a prefix that preserves its VM pin and
payload. Final resource destruction is not bypassed when only one owner exists. -/
theorem releaseOwned_retained_prefix {α : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token,handleType α,.nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id,typeName α,.tuple #[.integer 2,NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 2) :
    Result.ReadyPrefix (releaseOwned handle) env (.ok ()) {env with nativeHeap :=
      (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id,typeName α,.tuple #[.integer 1,NativeCodec.encode value]) else cell} := by
  exact releaseOwned_live_prefix handle value 2 env (by decide) (by decide) token stored owners

theorem releaseOwned_retained_handled_next {α β γ : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (finish : NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 2) :
    ((Result.handle (do releaseOwned handle; finish) handler) >>= next) env =
      ((Result.handle finish handler) >>= next) {env with nativeHeap :=
      (env.nativeHeap.filter fun cell => cell.1 != handle.token).map fun cell =>
        if cell.1 == handle.id then
          (handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value]) else cell } := by
  simp [releaseOwned, takeOwner, ownerState, ownedState, retiredState, release, takeOwner, ownerState, ownedState, retiredState, ownership, token, stored, owners,
    NativeCodec.roundtrip, referenceLimit, Result.handle]

/-- The unique final owner cleans up from the retired allocation state. The
cleanup contract must preserve whatever unrelated state its implementation requires. -/
theorem releaseOwned_last_run_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α]
    (handle : NativeResourceArc α) (value : α) (next : Unit → NativeM β) (env after : Environment)
    (policy : NativeResourceCleanup.observable (α := α) = false ∨ env.nativeFinalizerMode = .synchronous)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, handleType α, .nativeReference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference handle.id).length = 1)
    (cleaned : ∀ next : NativeM β,
      (do NativeResourceCleanup.cleanup value; next) (retiredState handle env) = next after) :
    (releaseOwned handle >>= next) env = next () after := by
  rw [releaseOwned_last_next handle value next env policy token stored owners]
  exact cleaned (next ())

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
    let .nativeReference id := (fields[0]'(by omega)) | none
    let .nativeReference token := (fields[1]'(by omega)) | none
    some ⟨id, token⟩
  else none

private def termOwner {α : Type} [NativeCodec α] (term : Term)
    (env : Environment) : Option (NativeResourceArc α) := do
  let .nativeReference identity := term | none
  let [cell] := env.nativeHeap.filter (fun cell => cell.1 == identity) | none
  termEntryOwner cell

/-- Model enif_make_resource: pin the allocation independently of its Rust owner.
Existing live terms for the same allocation share identity. No Rust owner is
consumed by Encoder::encode(&self); the generated wrapper drops it afterwards. -/
def encode {α : Type} [NativeCodec α] (handle : NativeResourceArc α) : NativeM Term :=
  .nativeGet fun env =>
    match ownership handle env with
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
          (.tuple #[.nativeReference pin.id, .nativeReference pin.token])
        .ok (.nativeReference identity)
      | [(identity, _, _)] =>
        match termOwner (α := α) (.nativeReference identity) env with
        | some pin => if (ownership pin env).isSome then .ok (.nativeReference identity)
            else .error .exhausted
        | none => .error .exhausted
      | _ => .error .exhausted

/-- Model ResourceArc::from_term: wrong terms/types produce badarg; a successful
conversion acquires a fresh Rust ownership token while preserving the VM pin.
An inconsistent internal heap is verification exhaustion. -/
def decode {α : Type} [NativeCodec α] (term : Term) : NativeM (NativeResourceArc α) :=
  .nativeGet fun env =>
    if typeName α ∈ env.nativeResourceTypes then
      match termOwner term env with
      | none => .error (.error (.atom "badarg"))
      | some pin => clone pin
    else .error (.error (.atom "badarg"))

/-- Public computation equation for resource decoding. Parsing helpers remain private. -/
@[cbv_eval] theorem decode_eq {α : Type} [NativeCodec α] (term : Term) :
    decode (α := α) term = .nativeGet (fun env =>
      if typeName α ∈ env.nativeResourceTypes then
        let owner : Option (NativeResourceArc α) := do
          let .nativeReference identity := term | none
          let [cell] := env.nativeHeap.filter (fun cell => cell.1 == identity) | none
          if cell.2.1 != termType α then none else
          let .tuple fields := cell.2.2 | none
          if size : fields.size = 2 then
            let .nativeReference id := (fields[0]'(by omega)) | none
            let .nativeReference token := (fields[1]'(by omega)) | none
            some ⟨id, token⟩
          else none
        match owner with
        | none => .error (.error (.atom "badarg"))
        | some pin => clone pin
      else .error (.error (.atom "badarg"))) := by
  rfl

/-- Public computation equation for resource encoding, including existing VM pins. -/
@[cbv_eval] theorem encode_eq {α : Type} [NativeCodec α] (handle : NativeResourceArc α) :
    encode handle = .nativeGet (fun env =>
      let entryOwner : (Nat × String × Term) → Option (NativeResourceArc α) := fun cell => do
        if cell.2.1 != termType α then none else
        let .tuple fields := cell.2.2 | none
        if size : fields.size = 2 then
          let .nativeReference id := (fields[0]'(by omega)) | none
          let .nativeReference token := (fields[1]'(by omega)) | none
          some ⟨id, token⟩
        else none
      match ownership handle env with
      | none => .error .exhausted
      | some _ =>
        let existing := env.nativeHeap.filter fun cell =>
          match entryOwner cell with
          | some owner => owner.id == handle.id
          | none => false
        match existing with
        | [] => do
          let pin ← clone handle
          let identity ← NativeM.allocate (termType α)
            (.tuple #[.nativeReference pin.id, .nativeReference pin.token])
          .ok (.nativeReference identity)
        | [(identity, _, _)] =>
          let owner : Option (NativeResourceArc α) := do
            let [cell] := env.nativeHeap.filter (fun cell => cell.1 == identity) | none
            entryOwner cell
          match owner with
          | some pin => if (ownership pin env).isSome then .ok (.nativeReference identity)
              else .error .exhausted
          | none => .error .exhausted
        | _ => .error .exhausted) := by
  rfl

/-- Decode through the surviving VM pin while other Rust owners are live.
The actual registry, allocation and owner-token count are checked together. -/
theorem decode_live_prefix {α : Type} [NativeCodec α]
    (pin : NativeResourceArc α) (term : Nat) (value : α) (count : Nat) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes)
    (positive : 0 < count) (bounded : count < referenceLimit)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term, termType α, .tuple #[.nativeReference pin.id, .nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token, handleType α, .nativeReference pin.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference pin.id).length = count)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    Result.ReadyPrefix (decode (.nativeReference term)) env
      (.ok (⟨pin.id, env.nativeRefCounter + 1⟩ : NativeResourceArc α)) {env with
        nativeRefCounter := env.nativeRefCounter + 1, nativeHeap :=
          (env.nativeRefCounter + 1, handleType α, .nativeReference pin.id) :: env.nativeHeap.map fun cell =>
            if cell.1 == pin.id then
              (pin.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value]) else cell} := by
  unfold decode
  apply Result.ReadyPrefix.nativeGet
  simp only [ite_eq_left registered, termOwner, registry, termEntryOwner]
  simpa using clone_live_prefix pin value count env positive bounded token stored owners fresh

/-- Decoder ownership changes are local steps; the residual is the actual
fresh handle and no subsequent lock or file poll is consumed. -/
theorem decode_live_registeredPrefix {α : Type} [NativeCodec α]
    (pid : PID) (pin : NativeResourceArc α) (term : Nat) (value : α) (count : Nat)
    (before : Nat × List (Nat × String × Term)) (types : List String)
    (registered : typeName α ∈ types)
    (positive : 0 < count) (bounded : count < referenceLimit)
    (registry : before.2.filter (fun cell => cell.1 == term) =
      [(term, termType α, .tuple #[.nativeReference pin.id, .nativeReference pin.token])])
    (token : before.2.filter (fun cell => cell.1 == pin.token) =
      [(pin.token, handleType α, .nativeReference pin.id)])
    (stored : before.2.filter (fun cell => cell.1 == pin.id) =
      [(pin.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference pin.id).length = count)
    (fresh : before.2.any (fun cell => cell.1 == before.1 + 1) = false) :
    Result.RegisteredPrefix pid (decode (.nativeReference term)) before types
      (.ok (⟨pin.id, before.1 + 1⟩ : NativeResourceArc α))
      (before.1 + 1, (before.1 + 1, handleType α, .nativeReference pin.id) :: before.2.map fun cell =>
        if cell.1 == pin.id then
          (pin.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value]) else cell) types := by
  unfold decode
  refine .read _ (clone pin) before _ types types _ ?_ ?_
  · intro env _ _ heap available
    simp [heap, available, registered, termOwner, registry, termEntryOwner]
  · unfold clone
    refine .modify _ Result.ofExcept (Except.ok ⟨pin.id, before.1 + 1⟩)
      before _ _ types types types _ ?_ (.refl _ _ _)
    intro env _ refs heap available
    have boundInt : (count : Int) ≤ referenceLimit := by exact_mod_cast Nat.le_of_lt bounded
    simp [ownership, heap, refs, token, stored, owners, NativeCodec.roundtrip, positive,
      boundInt, bounded, fresh, available]

/-- The actual decoder acquires an owner in a registered scheduler context.
Its local reads and write precede the continuation; no native wait or cleanup
inside that continuation is replaced with an atomic transition. -/
theorem decode_live_registeredSteps {α β : Type} [NativeCodec α]
    (pid : PID) (pin : NativeResourceArc α) (term : Nat) (value : α) (count : Nat)
    (before final : Nat × List (Nat × String × Term)) (types finalTypes : List String)
    (next : NativeResourceArc α → NativeM β) (answer : β)
    (registered : typeName α ∈ types)
    (positive : 0 < count) (bounded : count < referenceLimit)
    (registry : before.2.filter (fun cell => cell.1 == term) =
      [(term, termType α, .tuple #[.nativeReference pin.id, .nativeReference pin.token])])
    (token : before.2.filter (fun cell => cell.1 == pin.token) =
      [(pin.token, handleType α, .nativeReference pin.id)])
    (stored : before.2.filter (fun cell => cell.1 == pin.id) =
      [(pin.id, typeName α, .tuple #[.integer count, NativeCodec.encode value])])
    (owners : (before.2.filter fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference pin.id).length = count)
    (fresh : before.2.any (fun cell => cell.1 == before.1 + 1) = false)
    (rest : Result.RegisteredSteps pid (next ⟨pin.id, before.1 + 1⟩)
      (before.1 + 1, (before.1 + 1, handleType α, .nativeReference pin.id) :: before.2.map fun cell =>
        if cell.1 == pin.id then
          (pin.id, typeName α, .tuple #[.integer (count + 1), NativeCodec.encode value]) else cell)
      types answer final finalTypes) :
    Result.RegisteredSteps pid (decode (.nativeReference term) >>= next)
      before types answer final finalTypes := by
  have head := (decode_live_registeredPrefix pid pin term value count before types
    registered positive bounded registry token stored owners fresh).bind next
  simp only [Result.ok_bind] at head
  exact head.thenSteps rest

@[simp] theorem decode_nonreference {α : Type} [NativeCodec α] (term : Term)
    (notReference : ∀ identity, term ≠ .nativeReference identity) (env : Environment) :
    decode (α := α) term env = (.error (.error (.atom "badarg")), env) := by
  by_cases registered : typeName α ∈ env.nativeResourceTypes
  · cases term <;> simp_all [decode, termOwner]
  · simp [decode, registered]

/-- A rejected non-reference invokes the exception handler without allocating a
Rust owner or changing the heap, even inside a larger translated computation. -/
theorem decode_nonreference_handled_next {α β γ : Type} [NativeCodec α]
    (term : Term) (notReference : ∀ identity, term ≠ .nativeReference identity)
    (finish : NativeResourceArc α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment) (choices : List ScheduleChoice) :
    ((Result.handle (decode (α := α) term >>= finish) handler) >>= next).run env choices =
      (handler (.error (.atom "badarg")) >>= next).run env choices := by
  by_cases registered : typeName α ∈ env.nativeResourceTypes
  · cases term <;> simp_all [decode, termOwner, Result.handle,
      Result.nativeGet_bind, Result.nativeGet_continuation_run]
  · simp [decode, registered, Result.handle, Result.nativeGet_bind, Result.nativeGet_continuation_run]

/-- Rustler cannot recover a typed resource before its type is registered. -/
theorem decode_unregistered {α : Type} [NativeCodec α] (term : Term) (env : Environment)
    (absent : typeName α ∉ env.nativeResourceTypes) :
    decode (α := α) term env = (.error (.error (.atom "badarg")), env) := by
  simp [decode, absent]

/-- An ordinary reference without a resource registry cell is not a resource. -/
theorem decode_missing {α : Type} [NativeCodec α] (identity : Nat) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == identity) = []) :
    decode (α := α) (.nativeReference identity) env =
      (.error (.error (.atom "badarg")), env) := by
  by_cases registered : typeName α ∈ env.nativeResourceTypes <;>
    simp [decode, registered, termOwner, missing]

/-- A reference belonging to another nominal resource type cannot decode. -/
theorem decode_wrong_type {α : Type} [NativeCodec α] (identity : Nat)
    (env : Environment) (tag : String) (contents : Term)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == identity) = [(identity, tag, contents)])
    (different : tag ≠ termType α) :
    decode (α := α) (.nativeReference identity) env =
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
  simp [deref, ownership, missing]

theorem clone_missing {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    clone handle env = (.error .exhausted, env) := by
  simp [clone, ownership, missing]

/-- Releasing an already consumed token cannot decrement another owner's count. -/
theorem release_missing {α : Type} [NativeCodec α] (handle : NativeResourceArc α)
    (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    release handle env = (.error .exhausted, env) := by
  simp [release, takeOwner, ownerState, ownedState, retiredState, ownership, missing]

/-- A forged count cannot keep a resource alive without the corresponding owners. -/
theorem deref_inconsistent_count {α : Type} [NativeCodec α]
    (handle : NativeResourceArc α) (value : α) (env : Environment)
    (distinct : handle.id ≠ handle.token)
    (stored : env.nativeHeap = [
      (handle.token, handleType α, .nativeReference handle.id),
      (handle.id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])]) :
    deref handle env = (.error .exhausted, env) := by
  simp [deref, ownership, stored, distinct, Ne.symm distinct,
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
      next observed) env = next value { env with nativeRefCounter := env.nativeRefCounter + 3 } := by
  simp only [new, Result.nativeGet_bind, Result.nativeGet_continuation_apply, ite_eq_left registered]
  simp [clone, release, takeOwner, ownerState, ownedState, retiredState, deref, ownership, NativeM.allocate,
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
        (.ok value, { env with nativeRefCounter := env.nativeRefCounter + 3 }) := by
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
        { env with nativeRefCounter := env.nativeRefCounter + 3 } := by
  simp only [new, Result.nativeGet_bind, Result.handle, Result.nativeGet_continuation_apply,
    ite_eq_left registered]
  simp [clone, release, takeOwner, ownerState, ownedState, retiredState, deref, ownership, NativeM.allocate, Result.handle,
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
      next observed (term == again)) env = next value true { env with nativeRefCounter := env.nativeRefCounter + 5, nativeHeap := [
        (env.nativeRefCounter + 4, termType α,
          .tuple #[.nativeReference (env.nativeRefCounter + 1), .nativeReference (env.nativeRefCounter + 3)]),
        (env.nativeRefCounter + 3, handleType α, .nativeReference (env.nativeRefCounter + 1)),
        (env.nativeRefCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])] } := by
  simp only [new, Result.nativeGet_bind, Result.nativeGet_continuation_apply, ite_eq_left registered]
  simp only [typeName] at registered
  simp [encode, decode, termOwner, termEntryOwner, clone, release, takeOwner, ownerState, ownedState, retiredState, deref, ownership,
    NativeM.allocate, empty, NativeCodec.roundtrip, referenceLimit, handleType,
    typeName, termType, registered, Nat.add_assoc]

/-- A resource-visible frame cannot refer to identities above this counter.
Payload contents are opaque: only ownership tokens and VM registry references
are inspected by resource operations. This is not whole-runtime reachability. -/
@[expose] def FrameBelow (α : Type) [NativeCodec α] (limit : Nat)
    (frame : List (Nat × String × Term)) : Prop :=
  ∀ cell ∈ frame, cell.1 ≤ limit ∧
    (cell.2.1 = handleType α → ∀ target, cell.2.2 = .nativeReference target → target ≤ limit) ∧
    (cell.2.1 = termType α → ∀ fields, cell.2.2 = .tuple fields →
      ∀ target, Term.nativeReference target ∈ fields.toList → target ≤ limit)

/-- The three logical cells retained by an encoded immutable resource. -/
@[expose] def vmCells {α : Type} [NativeCodec α] (value : α) (id pin term : Nat) :
    List (Nat × String × Term) := [
  (term, termType α, .tuple #[.nativeReference id, .nativeReference pin]),
  (pin, handleType α, .nativeReference id),
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
    (value == .nativeReference id) = true ↔ value = .nativeReference id := by
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]

private theorem frame_tokens (frame : List (Nat × String × Term)) (limit id : Nat)
    {α : Type} [NativeCodec α] (bounded : FrameBelow α limit frame) (fresh : limit < id) :
    frame.filter (fun cell => cell.2.1 == handleType α && cell.2.2 == .nativeReference id) = [] := by
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
  ordered : id < pin ∧ pin < term ∧ term ≤ env.nativeRefCounter
  keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter
  allocation : env.nativeHeap.filter (fun cell => cell.1 == id) =
    [(id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])]
  owner : env.nativeHeap.filter (fun cell => cell.1 == pin) =
    [(pin, handleType α, .nativeReference id)]
  registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
    [(term, termType α, .tuple #[.nativeReference id, .nativeReference pin])]
  owners : (env.nativeHeap.filter (fun cell =>
    cell.2.1 == handleType α && cell.2.2 == .nativeReference id)).length = 1

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
      cell.2.1 == handleType α && cell.2.2 == .nativeReference id)).length =
    (heap.filter (fun cell => cell.2.1 == handleType α && cell.2.2 == .nativeReference id)).length := by
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
    (frame : FrameBelow α env.nativeRefCounter env.nativeHeap) :
    ((Result.handle (do
      let owner ← new value
      let term ← encode owner
      release owner
      Result.ok term) handler) >>= next) env =
    next (.nativeReference (env.nativeRefCounter + 4)) { env with
      nativeRefCounter := env.nativeRefCounter + 4
      nativeHeap := vmCells value (env.nativeRefCounter + 1) (env.nativeRefCounter + 3)
        (env.nativeRefCounter + 4) ++ env.nativeHeap } := by
  have keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter := fun cell member =>
    (frame cell member).1
  have ids1 := frame_filter_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have anys1 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have ids2 := frame_filter_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 2) keys (by omega)
  have anys2 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 2) keys (by omega)
  have anys3 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 3) keys (by omega)
  have anys4 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 4) keys (by omega)
  have removes := frame_filter_ne env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 2) keys (by omega)
  have mapTwo := frame_map_update env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    (fun _ => (env.nativeRefCounter + 1, typeName α, .tuple #[.integer 2, NativeCodec.encode value])) keys (by omega)
  have mapOne := frame_map_update env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    (fun _ => (env.nativeRefCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])) keys (by omega)
  have tokens := frame_tokens env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) frame (by omega)
  have terms := frame_terms env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) frame (by omega)
  simp only [handleType] at tokens
  simp only [termEntryOwner, termType, bne_iff_ne, ite_not] at terms
  simp only [typeName, beq_iff_eq] at mapTwo mapOne
  simp only [new, Result.handle, Result.nativeGet_bind, Result.nativeGet_continuation_apply,
    ite_eq_left registered]
  simp [encode, termOwner, termEntryOwner, clone, release, takeOwner, ownerState, ownedState, retiredState, ownership,
    NativeM.allocate, Result.handle, vmCells, ids1, ids2,
    removes, mapTwo, mapOne, anys1, anys2, anys3, anys4, tokens, terms,
    NativeCodec.roundtrip, referenceLimit,
    handleType, typeName, termType, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
/-- Owned structural cleanup also preserves the VM pin on successful resource return.
No pre-existing owner or VM registry may refer to the newly allocated identities. -/
theorem newOwned_encode_release_framed_run {α β : Type} [NativeCodec α] [NativeResourceCleanup α] (value : α)
    (handler : Exception → NativeM Term) (next : Term → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes)
    (frame : FrameBelow α env.nativeRefCounter env.nativeHeap) (choices : List ScheduleChoice) :
    ((Result.handle (do
      let owner ← newOwned value
      let term ← encode owner
      releaseOwned owner
      Result.ok term) handler) >>= next).run env choices =
    (next (.nativeReference (env.nativeRefCounter + 4))).run { env with
      nativeRefCounter := env.nativeRefCounter + 4
      nativeHeap := vmCells value (env.nativeRefCounter + 1) (env.nativeRefCounter + 3)
        (env.nativeRefCounter + 4) ++ env.nativeHeap } choices := by
  have keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter := fun cell member =>
    (frame cell member).1
  have ids1 := frame_filter_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have anys1 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) keys (by omega)
  have ids2 := frame_filter_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 2) keys (by omega)
  have anys2 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 2) keys (by omega)
  have anys3 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 3) keys (by omega)
  have anys4 := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 4) keys (by omega)
  have removes := frame_filter_ne env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 2) keys (by omega)
  have mapTwo := frame_map_update env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    (fun _ => (env.nativeRefCounter + 1, typeName α, .tuple #[.integer 2, NativeCodec.encode value])) keys (by omega)
  have mapOne := frame_map_update env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    (fun _ => (env.nativeRefCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])) keys (by omega)
  have tokens := frame_tokens env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) frame (by omega)
  have terms := frame_terms env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1) frame (by omega)
  simp only [handleType] at tokens
  simp only [termEntryOwner, termType, bne_iff_ne, ite_not] at terms
  simp only [typeName, beq_iff_eq] at mapTwo mapOne
  simp only [newOwned, new, Result.handle, Result.nativeGet_bind, Result.nativeGet_continuation_run,
    ite_eq_left registered]
  simp [encode, termOwner, termEntryOwner, clone, releaseOwned, takeOwner, ownerState, ownedState, retiredState, release, takeOwner, ownerState, ownedState, retiredState, ownership,
    NativeM.allocate, Result.handle, vmCells, ids1, ids2,
    removes, mapTwo, mapOne, anys1, anys2, anys3, anys4, tokens, terms,
    NativeCodec.roundtrip, referenceLimit,
    handleType, typeName, termType, Nat.add_assoc]

set_option maxHeartbeats 1000000 in
/-- Owned structural cleanup also preserves the VM pin on successful resource return.
No pre-existing owner or VM registry may refer to the newly allocated identities. -/
theorem newOwned_encode_release_framed_next {α β : Type} [NativeCodec α] [NativeResourceCleanup α] (value : α)
    (handler : Exception → NativeM Term) (next : Term → NativeM β) (env : Environment)
    (registered : typeName α ∈ env.nativeResourceTypes)
    (frame : FrameBelow α env.nativeRefCounter env.nativeHeap) :
    ((Result.handle (do
      let owner ← newOwned value
      let term ← encode owner
      releaseOwned owner
      Result.ok term) handler) >>= next) env =
    next (.nativeReference (env.nativeRefCounter + 4)) { env with
      nativeRefCounter := env.nativeRefCounter + 4
      nativeHeap := vmCells value (env.nativeRefCounter + 1) (env.nativeRefCounter + 3)
        (env.nativeRefCounter + 4) ++ env.nativeHeap } := by
  exact newOwned_encode_release_framed_run value handler next env registered frame []

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
    next (.nativeReference (env.nativeRefCounter + 4)) { env with nativeRefCounter := env.nativeRefCounter + 4, nativeHeap := [
      (env.nativeRefCounter + 4, termType α,
        .tuple #[.nativeReference (env.nativeRefCounter + 1), .nativeReference (env.nativeRefCounter + 3)]),
      (env.nativeRefCounter + 3, handleType α, .nativeReference (env.nativeRefCounter + 1)),
      (env.nativeRefCounter + 1, typeName α, .tuple #[.integer 1, NativeCodec.encode value])] } := by
  simp only [new, Result.handle, Result.nativeGet_bind, Result.nativeGet_continuation_apply,
    ite_eq_left registered]
  simp [encode, termOwner, termEntryOwner, clone, release, takeOwner, ownerState, ownedState, retiredState, ownership,
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
      let owner ← decode (α := α) (.nativeReference term)
      let result ← Result.handle (do
        let observed ← deref owner
        release owner
        finish observed) handler
      next result) env =
      ((Result.handle (finish value) handler) >>= next)
        {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  have a : id ≠ pin := by have := pinned.ordered; omega
  have b : id ≠ term := by have := pinned.ordered; omega
  have c : pin ≠ term := by have := pinned.ordered; omega
  have d : env.nativeRefCounter + 1 ≠ id := by have := pinned.ordered; omega
  have e : env.nativeRefCounter + 1 ≠ pin := by have := pinned.ordered; omega
  have f : env.nativeRefCounter + 1 ≠ term := by have := pinned.ordered; omega
  let changed := env.nativeHeap.map (replaceCell id (typeName α)
    (.tuple #[.integer 2, NativeCodec.encode value]))
  have allocation2 : changed.filter (fun cell => cell.1 == id) =
      [(id, typeName α, .tuple #[.integer 2, NativeCodec.encode value])] := by
    simp [changed, filter_replace, pinned.allocation, replaceCell]
  have owner2 : changed.filter (fun cell => cell.1 == pin) =
      [(pin, handleType α, .nativeReference id)] := by
    simp [changed, filter_replace, pinned.owner, replaceCell, a, Ne.symm a]
  have fresh := frame_filter_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    pinned.keys (by omega)
  have absent2 : changed.filter (fun cell => cell.1 == env.nativeRefCounter + 1) = [] := by
    simp [changed, filter_replace, fresh]
  have anyFresh := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    pinned.keys (by omega)
  have count2 : (changed.filter (fun cell =>
      cell.2.1 == handleType α && cell.2.2 == .nativeReference id)).length = 1 := by
    rw [show changed = _ from rfl, replace_token_count env.nativeHeap id
      (.tuple #[.integer 1, NativeCodec.encode value]) _ pinned.allocation]
    exact pinned.owners
  have removeFresh := frame_filter_ne env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    pinned.keys (by omega)
  have removes : changed.filter (fun cell => cell.1 != env.nativeRefCounter + 1) = changed := by
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
  simp [decode, registered, termOwner, termEntryOwner, clone, release, takeOwner, ownerState, ownedState, retiredState, deref,
    ownership, Result.handle, allocation, owner, registry, owners,
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
    (decode (α := α) (.nativeReference term) >>= next) env =
      next ⟨id, env.nativeRefCounter + 1⟩ { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := (env.nativeRefCounter + 1, handleType α, .nativeReference id) ::
          env.nativeHeap.map fun cell => if cell.1 == id then
            (id, typeName α, .tuple #[.integer 2, NativeCodec.encode value]) else cell } := by
  have a : id ≠ pin := by have := pinned.ordered; omega
  have b : id ≠ term := by have := pinned.ordered; omega
  have c : pin ≠ term := by have := pinned.ordered; omega
  have d : env.nativeRefCounter + 1 ≠ id := by have := pinned.ordered; omega
  have e : env.nativeRefCounter + 1 ≠ pin := by have := pinned.ordered; omega
  have f : env.nativeRefCounter + 1 ≠ term := by have := pinned.ordered; omega
  have anyFresh := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    pinned.keys (by omega)
  have allocation := pinned.allocation
  have owner := pinned.owner
  have registry := pinned.registry
  have owners := pinned.owners
  simp only [typeName] at registered
  simp only [typeName, handleType, termType] at allocation owner registry owners
  simp [decode, registered, termOwner, termEntryOwner, clone, ownership,
    allocation, owner, registry, owners, anyFresh, NativeCodec.roundtrip,
    referenceLimit, typeName, handleType, termType, a, b, c, d, e, f,
    Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f]

/-- Successful resource decoding is an actual prefix through registry checking,
VM-pin ownership and allocation of a distinct Rust owner. -/
theorem decode_pinned_prefix {α : Type} [NativeCodec α]
    (value : α) (env : Environment) (id pin term : Nat) (pinned : Pinned value id pin term env)
    (registered : typeName α ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (decode (α := α) (.nativeReference term)) env
      (.ok ⟨id,env.nativeRefCounter + 1⟩) {env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := (env.nativeRefCounter + 1,handleType α,.nativeReference id) ::
          env.nativeHeap.map fun cell => if cell.1 == id then
            (id,typeName α,.tuple #[.integer 2,NativeCodec.encode value]) else cell} := by
  have anyFresh := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    pinned.keys (by omega)
  have allocation := pinned.allocation
  have owner := pinned.owner
  have registry := pinned.registry
  have owners := pinned.owners
  simp only [typeName] at registered
  simp only [typeName, handleType, termType] at allocation owner registry owners
  unfold decode
  apply Result.ReadyPrefix.nativeGet
  simp [registered,termOwner,termEntryOwner,registry,termType,typeName]
  simpa [typeName] using clone_live_prefix (⟨id,pin⟩ : NativeResourceArc α) value 1 env
    (by decide) (by decide) owner allocation owners anyFresh


theorem decode_pinned_handled_next {α β γ : Type} [NativeCodec α]
    (value : α) (finish : NativeResourceArc α → NativeM β)
    (handler : Exception → NativeM β) (next : β → NativeM γ)
    (env : Environment) (id pin term : Nat) (pinned : Pinned value id pin term env)
    (registered : typeName α ∈ env.nativeResourceTypes) :
    ((Result.handle (decode (α := α) (.nativeReference term) >>= finish) handler) >>= next) env =
      ((Result.handle (finish ⟨id, env.nativeRefCounter + 1⟩) handler) >>= next) { env with
        nativeRefCounter := env.nativeRefCounter + 1
        nativeHeap := (env.nativeRefCounter + 1, handleType α, .nativeReference id) ::
          env.nativeHeap.map fun cell => if cell.1 == id then
            (id, typeName α, .tuple #[.integer 2, NativeCodec.encode value]) else cell } := by
  have a : id ≠ pin := by have := pinned.ordered; omega
  have b : id ≠ term := by have := pinned.ordered; omega
  have c : pin ≠ term := by have := pinned.ordered; omega
  have d : env.nativeRefCounter + 1 ≠ id := by have := pinned.ordered; omega
  have e : env.nativeRefCounter + 1 ≠ pin := by have := pinned.ordered; omega
  have f : env.nativeRefCounter + 1 ≠ term := by have := pinned.ordered; omega
  have anyFresh := frame_any_id env.nativeHeap env.nativeRefCounter (env.nativeRefCounter + 1)
    pinned.keys (by omega)
  have allocation := pinned.allocation
  have owner := pinned.owner
  have registry := pinned.registry
  have owners := pinned.owners
  simp only [typeName] at registered
  simp only [typeName, handleType, termType] at allocation owner registry owners
  simp [Result.handle, decode, registered, termOwner, termEntryOwner, clone, ownership,
    allocation, owner, registry, owners, anyFresh, NativeCodec.roundtrip,
    referenceLimit, typeName, handleType, termType, a, b, c, d, e, f,
    Ne.symm a, Ne.symm b, Ne.symm c, Ne.symm d, Ne.symm e, Ne.symm f]

set_option maxHeartbeats 800000 in
/-- Decoding a live VM term temporarily acquires a Rust owner. Reading and
releasing it preserves the VM pin and contents, including across NIF calls. -/
theorem decode_read_release_handled_next {α β γ : Type} [NativeCodec α]
    (value : α) (finish : α → NativeM β) (handler : Exception → NativeM β)
    (next : β → NativeM γ) (env : Environment) (id pin term : Nat)
    (ordered : id < pin ∧ pin < term ∧ term ≤ env.nativeRefCounter)
    (stored : env.nativeHeap = [
      (term, termType α, .tuple #[.nativeReference id, .nativeReference pin]),
      (pin, handleType α, .nativeReference id),
      (id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (registered : typeName α ∈ env.nativeResourceTypes) :
    (do
      let owner ← decode (α := α) (.nativeReference term)
      let result ← Result.handle (do
        let observed ← deref owner
        release owner
        finish observed) handler
      next result) env =
      ((Result.handle (finish value) handler) >>= next)
        {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  have a : id ≠ pin := by omega
  have b : id ≠ term := by omega
  have c : pin ≠ term := by omega
  have d : env.nativeRefCounter + 1 ≠ id := by omega
  have e : env.nativeRefCounter + 1 ≠ pin := by omega
  have f : env.nativeRefCounter + 1 ≠ term := by omega
  simp only [typeName] at registered
  simp [decode, registered, termOwner, termEntryOwner, clone, release, takeOwner, ownerState, ownedState, retiredState, deref, ownership,
    Result.handle, stored, NativeCodec.roundtrip, referenceLimit, handleType,
    typeName, termType, a, b, c, d, Ne.symm a, Ne.symm b, Ne.symm c,
    Ne.symm d, Ne.symm e, Ne.symm f]

set_option maxHeartbeats 800000 in
/-- If a subsequent argument decoder fails, releasing the acquired Rust owner
before propagating badarg preserves the VM pin and resource contents. -/
theorem decode_failure_cleanup_handled_next {α β γ : Type} [NativeCodec α]
    (value : α) (handler : Exception → NativeM β) (next : β → NativeM γ)
    (env : Environment) (id pin term : Nat)
    (ordered : id < pin ∧ pin < term ∧ term ≤ env.nativeRefCounter)
    (stored : env.nativeHeap = [
      (term, termType α, .tuple #[.nativeReference id, .nativeReference pin]),
      (pin, handleType α, .nativeReference id),
      (id, typeName α, .tuple #[.integer 1, NativeCodec.encode value])])
    (registered : typeName α ∈ env.nativeResourceTypes) :
    ((Result.handle (do
      let owner ← decode (α := α) (.nativeReference term)
      release owner
      Result.error (.error (.atom "badarg"))) handler) >>= next) env =
      (handler (.error (.atom "badarg")) >>= next)
        {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  have a : id ≠ pin := by omega
  have b : id ≠ term := by omega
  have c : pin ≠ term := by omega
  have d : env.nativeRefCounter + 1 ≠ id := by omega
  have e : env.nativeRefCounter + 1 ≠ pin := by omega
  have f : env.nativeRefCounter + 1 ≠ term := by omega
  simp only [typeName] at registered
  simp [decode, registered, termOwner, termEntryOwner, clone, release, takeOwner, ownerState, ownedState, retiredState, ownership,
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
  if waker.id ≤ env.nativeRefCounter ∧ (cells == [(waker.id, typeName, .atom "idle")] ||
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
    (bounded : waker.id ≤ env.nativeRefCounter)
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
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp

/-- The wake request composes with the actual caller's continuation. -/
theorem wakeByRef_registered_next {α : Type} (waker : NativeWaker)
    (next : Unit → Result α) (env : Environment)
    (bounded : waker.id ≤ env.nativeRefCounter)
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
  rw [Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
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
  rw [Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
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
    if waker.id ≤ env.nativeRefCounter ∧ tag = typeName ∧ (status = "idle" ∨ status = "notified") then
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
    (bounded : waker.id ≤ env.nativeRefCounter) (active : cancelled env = false)
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
  rw [Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp

theorem await_cancelled_next {α : Type} (waker : NativeWaker)
    (cancelled : Environment → Bool) (next : Signal → NativeM α) (env : Environment)
    (bounded : waker.id ≤ env.nativeRefCounter) (requested : cancelled env = true)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "notified")])
    (registered : waker.isNoop = false) :
    (await waker cancelled >>= next) env = next .cancel env := by
  have ready : pollAwait waker cancelled env = some (.ok .cancel, env) := by
    simp [pollAwait, registered, bounded, stored, requested]
  unfold await
  rw [Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp

theorem pollAwait_idle (waker : NativeWaker) (cancelled : Environment → Bool)
    (env : Environment) (bounded : waker.id ≤ env.nativeRefCounter) (active : cancelled env = false)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "idle")])
    (registered : waker.isNoop = false) :
    pollAwait waker cancelled env = none := by
  simp [pollAwait, registered, bounded, stored, active]

theorem await_cancelled_idle_next {α : Type} (waker : NativeWaker)
    (cancelled : Environment → Bool) (next : Signal → NativeM α) (env : Environment)
    (bounded : waker.id ≤ env.nativeRefCounter) (requested : cancelled env = true)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == waker.id) =
      [(waker.id, typeName, .atom "idle")])
    (registered : waker.isNoop = false) :
    (await waker cancelled >>= next) env = next .cancel env := by
  have ready : pollAwait waker cancelled env = some (.ok .cancel, env) := by
    simp [pollAwait, registered, bounded, stored, requested]
  unfold await
  rw [Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ ready]
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

/-- Internal heap representation of a borrowed file capability, not a Rustler
codec or a native descriptor. File contents remain in their independent cell. -/
instance : NativeCodec NativeFile where
  typeName := "std::fs::File:borrowed-capability-v1"
  encode file := .nativeReference file.id
  decode
    | .nativeReference id => some ⟨id⟩
    | _ => none
  decode_encode file := by cases file; rfl

/-- Opaque I/O error identity. Payload and kind remain external. Only a separately
admitted callback-free OS error capability has a consuming cleanup model. -/
structure NativeIoError where
  identity : Nat

/-- Internal identity representation only; this does not decode a Rustler argument
or assert that an arbitrary error is safe to destroy. -/
instance : NativeCodec NativeIoError where
  typeName := "core::io::error::Error:os-capability-v1"
  encode error := .nativeReference error.identity
  decode
    | .nativeReference identity => some ⟨identity⟩
    | _ => none
  decode_encode error := by cases error; rfl

namespace NativeIoError

/-- Elaboration support for an unused standard Debug dictionary. The Rust audit
rejects every actual call to this method; no formatting outcome is established. -/
@[expose] def debugUnavailable (_ : NativeIoError) (_ : core.fmt.Formatter) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) := .fail .undef

/-- Host admission asserts that this error contains no user destructor callback.
Native payload reclamation and allocator behavior remain trusted boundaries. -/
@[expose] def typeName : String := "rust:os-io-error"

/-- Consume one unique live admitted OS error. Missing, stale, wrong-type,
ambiguous or custom-payload identities exhaust verification instead of erasing
an unknown destructor. The admitted std/allocator cleanup is nonpanicking. -/
@[expose] def dispose (error : NativeIoError) : NativeM Unit :=
  Result.consumeNativeCapability typeName error.identity

end NativeIoError

instance : NativeDrop NativeIoError where
  drop := NativeIoError.dispose

instance : NativeOwnedDrop NativeIoError where
  drop := NativeIoError.dispose

namespace NativeFile

@[expose] def asRefStr (path : Str) : RustM Str := RustM.ok path

@[expose] def asRefShared {T U : Type} (inst : core.convert.AsRef T U) (value : T) : RustM U :=
  inst.as_ref value

@[expose] def typeName : String := "rust:regular-file"
@[expose] def closedTypeName : String := "rust:closed-file"
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
          durable.size > limit || position.toNat > limit then none
      else some ⟨visible, durable, position.toNat, fields[3]'(by omega)⟩
    else none
  | _ => none

/-- A mask selects each byte from the previous persistent image or current visible
image. Length may advance or shrink between the durable and visible lengths.
This assumes bytewise old/new tearing, with no device corruption or namespace loss. -/
@[expose] def persist (old visible mask : ByteArray) : Option ByteArray :=
  if min old.size visible.size ≤ mask.size ∧ mask.size ≤ max old.size visible.size ∧
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

/-- Set the visible length, preserving the prefix and zero-filling extension.
The descriptor offset is unchanged. Durability still requires synchronization. -/
@[expose] def resize (data : ByteArray) (length : Nat) : ByteArray :=
  ⟨(data.data.toList.take length ++ List.replicate (length - data.size) 0).toArray⟩

@[expose] def setLenStep (state : State) (length : U64) :
    Option (core.result.Result Unit NativeIoError × State) := do
  if length.val > limit then none else do
  let (success, value, mask, rest) ← action "set_len" state.script
  if success then
    if value != 0 then none else do
      let visible := resize state.visible length.val
      let durable ← persist state.durable visible mask
      some (.Ok (), {state with visible := visible, durable := durable, script := rest})
  else do
    let durable ← persist state.durable state.visible mask
    some (.Err ⟨value⟩, {state with durable := durable, script := rest})

/-- Named files use one inode image and distinct handle offsets/scripts. A
pre-admitted independent file remains an explicitly disjoint host capability. -/
@[expose] def inodeTypeName : String := "rust:file-inode"
@[expose] def handleTypeName : String := "rust:file-handle:read"
@[expose] def writableHandleTypeName : String := "rust:file-handle:read-write"
@[expose] def closedHandleTypeName : String := "rust:file-handle:closed"
@[expose] def namespaceTypeName : String := "rust:file-namespace"
@[expose] def directoryTypeName : String := "rust:file-directory"
@[expose] def closedDirectoryTypeName : String := "rust:file-directory:closed"

structure Handle where
  inode : Nat
  position : Nat
  script : Term

@[expose] def encodeHandle (handle : Handle) : Term :=
  .tuple #[.nativeReference handle.inode, .integer handle.position, handle.script]

@[expose] def decodeHandle : Term → Option Handle
  | .tuple fields => do
    if size : fields.size = 3 then
      let .nativeReference inode := fields[0]'(by omega) | none
      let .integer position := fields[1]'(by omega) | none
      if inode = 0 || position < 0 || position.toNat > limit then none
      else some ⟨inode, position.toNat, fields[2]'(by omega)⟩
    else none
  | _ => none

@[expose, simp] def getHandle (file : NativeFile) (tag : String) (env : Environment) : Option Handle := do
  if file.id = 0 || file.id > env.nativeRefCounter then none else
  match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
  | [(_, actual, contents)] => if actual == tag then decodeHandle contents else none
  | _ => none

@[expose] def inode (id : Nat) (env : Environment) : Option State := do
  if id = 0 || id > env.nativeRefCounter then none else
  match env.nativeHeap.filter (fun cell => cell.1 == id) with
  | [(_, tag, contents)] =>
    if tag == inodeTypeName then do
      let state ← decode contents
      if state.position = 0 && state.script == .nil then some state else none
    else none
  | _ => none

@[expose] def sharedLookup (file : NativeFile) (tag : String) (env : Environment) : Option State := do
  let handle ← getHandle file tag env
  let state ← inode handle.inode env
  some {state with position := handle.position, script := handle.script}

@[expose] def sharedStore (file : NativeFile) (handle : Handle) (state : State)
    (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == file.id then
      (file.id, cell.2.1, encodeHandle {handle with position := state.position, script := state.script})
    else if cell.1 == handle.inode then
      (handle.inode, inodeTypeName, encode {state with position := 0, script := .nil})
    else cell}

/-- Portable, single-component ASCII names, at most 255 bytes. Path traversal,
symlinks, directories, OS-specific path encodings and ambient cwd changes are
outside this closed namespace model and exhaust verification. -/
@[expose] def supportedPath (path : ByteArray) : Bool :=
  0 < path.size && path.size ≤ 255 && path.data != #[46] && path.data != #[46,46] &&
    path.data.toList.all (fun byte =>
      (48 ≤ byte && byte ≤ 57) || (65 ≤ byte && byte ≤ 90) || (97 ≤ byte && byte ≤ 122) ||
      byte == 45 || byte == 46 || byte == 95)

@[expose] def namespaceEntry : Term → Option (ByteArray × Nat)
  | .tuple fields => do
    if size : fields.size = 2 then
      let .bitstring path bits _ := fields[0]'(by omega) | none
      let .nativeReference id := fields[1]'(by omega) | none
      if bits != 0 || id = 0 || !supportedPath path then none else some (path,id)
    else none
  | _ => none

/-- Names are bounded independently of file size. The synchronized checkpoint
and pending snapshots are separate from the currently visible directory table. -/
abbrev Names := List (ByteArray × Nat)

structure NamespaceSnapshot where
  names : Names
  committed : Names
  pending : List Names
  script : Term

@[expose] def encodeNames (names : Names) : Term :=
  .tuple (names.map (fun (path,id) => .tuple #[.bitstring path 0, .nativeReference id])).toArray

@[expose] def namespaceTable : Term → Option Names
  | .tuple entries => do
    if entries.size > 1024 then none else do
      let names ← entries.toList.mapM namespaceEntry
      if (names.map (fun entry => entry.1.data)).eraseDups.length != names.length then none
      else some names
  | _ => none

@[expose] def namespaceHistory : Term → Option (List Names)
  | .nil => some []
  | .cons head tail => do
    let names ← namespaceTable head
    let rest ← namespaceHistory tail
    if rest.length ≥ 1024 then none else some (names :: rest)
  | _ => none

@[expose] def tablesEqual (left right : Names) : Bool :=
  (left.map (fun entry => (entry.1.data,entry.2))) ==
    (right.map (fun entry => (entry.1.data,entry.2)))

@[expose] def encodeNamespace (state : NamespaceSnapshot) : Term :=
  .tuple #[encodeNames state.names, encodeNames state.committed,
    state.pending.foldr (fun names tail => .cons (encodeNames names) tail) .nil, state.script]

/-- The committed table is the last synchronized checkpoint. Pending snapshots
record unsynchronized namespace versions that may also reach disk; the checkpoint
is not a claim that later versions remain physically volatile. Reads and opens
do not establish a new synchronization checkpoint. Host admission and filesystem
persistence correspondence remain external boundaries. -/
@[expose] def namespaceSnapshot (env : Environment) : Option NamespaceSnapshot := do
  match env.nativeHeap.filter (fun cell => cell.1 == 0) with
  | [(_, tag, .tuple fields)] =>
    if tag == namespaceTypeName then
      if size : fields.size = 4 then do
        let names ← namespaceTable (fields[0]'(by omega))
        let committed ← namespaceTable (fields[1]'(by omega))
        let pending ← namespaceHistory (fields[2]'(by omega))
        let latest := pending.getLast?.getD committed
        if !tablesEqual latest names then none
        else some ⟨names, committed, pending, fields[3]'(by omega)⟩
      else none
    else none
  | _ => none

@[expose] def namespaceState (env : Environment) : Option (Names × Term) := do
  let state ← namespaceSnapshot env
  some (state.names,state.script)

@[expose] def storeNamespace (state : NamespaceSnapshot) (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == 0 then (0, namespaceTypeName, encodeNamespace state) else cell}

@[expose] def replaceNamespaceScript (script : Term) (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == 0 then match cell.2.2 with
      | .tuple fields => (0, namespaceTypeName, .tuple (fields.set! 3 script))
      | _ => cell
    else cell}

/-- Each outcome names the actual requested path and gives an independent
script for the new handle: (open, path, ok|error, error-identity, handle-script). -/
@[expose] def pathChoice (expected : String) (path : ByteArray) : Term → Option (Bool × Nat × Term × Term)
  | .cons (.tuple fields) rest => do
    if size : fields.size = 5 then
      let .atom operation := fields[0]'(by omega) | none
      let .bitstring requested bits _ := fields[1]'(by omega) | none
      let .atom status := fields[2]'(by omega) | none
      let .integer error := fields[3]'(by omega) | none
      if operation != expected || bits != 0 || requested.data != path.data || error < 0 ||
          (status != "ok" && status != "error") then none
      else some (status == "ok", error.toNat, fields[4]'(by omega), rest)
    else none
  | _ => none

@[expose] def openChoice (path : ByteArray) : Term → Option (Bool × Nat × Term × Term) :=
  pathChoice "open" path

/-- Exclusive creation allocates a new inode and read/write handle. The name is
visible but is only a pending namespace snapshot; successful creation is not a
persistence guarantee. A reported success for an existing name is rejected. -/
@[expose] def pollCreateNew (path : Str) (env : Environment) :
    Option (Except Exception (core.result.Result NativeFile NativeIoError) × Environment) :=
  let invalid := some (.error .exhausted, env)
  let path := bytes path
  if !supportedPath path then invalid else
  match namespaceSnapshot env with
  | none => invalid
  | some state =>
    if state.script matches .cons (.atom "blocked") _ then none else
    match pathChoice "create_new" path state.script with
    | none => invalid
    | some (success, error, ioScript, rest) =>
      if !success then some (.ok (.Err ⟨error⟩), replaceNamespaceScript rest env)
      else if error != 0 || state.names.any (fun entry => entry.1.data == path.data) ||
          state.names.length ≥ 1024 || state.pending.length ≥ 1024 then invalid
      else
        let node := env.nativeRefCounter + 1
        let handle := node + 1
        if env.nativeHeap.any (fun cell => cell.1 == node || cell.1 == handle) then invalid
        else
          let names := state.names ++ [(path,node)]
          let changed := storeNamespace {state with
            names := names
            pending := state.pending ++ [names]
            script := rest} env
          some (.ok (.Ok ⟨handle⟩), {changed with
            nativeRefCounter := handle
            nativeHeap := (handle, writableHandleTypeName, encodeHandle ⟨node,0,ioScript⟩) ::
              (node, inodeTypeName, encode ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩) :: changed.nativeHeap})

@[expose] def createNew (path : Str) : NativeM (core.result.Result NativeFile NativeIoError) :=
  .wait (pollCreateNew path) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- Rename outcomes retain the requested pair of names and an explicit atomic
namespace effect. An error may have applied the operation; callers cannot assume
that an I/O error rolls back metadata. -/
@[expose] def renameChoice (source target : ByteArray) :
    Term → Option (Bool × Nat × Bool × Term)
  | .cons (.tuple fields) rest => do
    if size : fields.size = 6 then
      let .atom operation := fields[0]'(by omega) | none
      let .bitstring requestedSource fromBits _ := fields[1]'(by omega) | none
      let .bitstring requestedTarget toBits _ := fields[2]'(by omega) | none
      let .atom status := fields[3]'(by omega) | none
      let .integer error := fields[4]'(by omega) | none
      let .atom effect := fields[5]'(by omega) | none
      if operation != "rename" || fromBits != 0 || toBits != 0 ||
          requestedSource.data != source.data || requestedTarget.data != target.data || error < 0 ||
          (status != "ok" && status != "error") || (effect != "apply" && effect != "keep") then none
      else some (status == "ok", error.toNat, effect == "apply", rest)
    else none
  | _ => none

@[expose] def renamedNames (names : Names) (source target : ByteArray) (node : Nat) : Names :=
  names.filter (fun entry => entry.1.data != source.data && entry.1.data != target.data) ++ [(target,node)]

/-- Single-directory atomic replacement over regular inodes. Inode data and
open handles survive rename/unlink of a name. Same-inode aliases are unchanged.
Physical Unix/filesystem atomicity and error correspondence are external models. -/
@[expose] def pollRename (source target : Str) (env : Environment) :
    Option (Except Exception (core.result.Result Unit NativeIoError) × Environment) :=
  let invalid := some (.error .exhausted, env)
  let source := bytes source
  let target := bytes target
  if !supportedPath source || !supportedPath target then invalid else
  match namespaceSnapshot env with
  | none => invalid
  | some state =>
    if state.script matches .cons (.atom "blocked") _ then none else
    match renameChoice source target state.script with
    | none => invalid
    | some (success,error,applied,rest) =>
      if success && (error != 0 || !applied) then invalid else
      let reply := if success then core.result.Result.Ok () else .Err ⟨error⟩
      if !applied then some (.ok reply, replaceNamespaceScript rest env) else
      match state.names.filter (fun entry => entry.1.data == source.data) with
      | [(_,node)] =>
        match inode node env with
        | none => invalid
        | some _ =>
          let destination := state.names.filter (fun entry => entry.1.data == target.data)
          if destination.any (fun entry => (inode entry.2 env).isNone) then invalid else
          if destination.any (fun entry => entry.2 == node) then
            some (.ok reply, replaceNamespaceScript rest env)
          else if state.pending.length ≥ 1024 then invalid else
            let names := renamedNames state.names source target node
            some (.ok reply, storeNamespace {state with
              names := names
              pending := state.pending ++ [names]
              script := rest} env)
      | _ => invalid

@[expose] def rename (source target : Str) : NativeM (core.result.Result Unit NativeIoError) :=
  .wait (pollRename source target) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- Only the admitted current directory is supported in addition to regular
portable leaf names. Ambient cwd changes and nested/symlink traversal are closed. -/
@[expose] def supportedOpenPath (path : ByteArray) : Bool :=
  supportedPath path || path.data == #[46]

@[expose] def directoryHandle (file : NativeFile) (env : Environment) : Option Term := do
  if file.id = 0 || file.id > env.nativeRefCounter then none else
  match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
  | [(_,tag,.tuple fields)] =>
    if tag == directoryTypeName then
      if size : fields.size = 1 then some (fields[0]'(by omega)) else none
    else none
  | _ => none

@[expose] def storeDirectory (file : NativeFile) (tag : String) (script : Term)
    (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == file.id then (file.id,tag,.tuple #[script]) else cell}

/-- Directory fsync commits the visible namespace checkpoint and clears pending
metadata snapshots on success. It does not synchronize regular-file contents.
On error the last guaranteed checkpoint is unchanged; unsynchronized snapshots
may still have reached disk. Filesystem/device fsync correspondence is assumed. -/
@[expose] def pollDirectorySync (file : NativeFile) (env : Environment) :
    Option (Except Exception (core.result.Result Unit NativeIoError) × Environment) :=
  let invalid := some (.error .exhausted,env)
  match directoryHandle file env with
  | none => invalid
  | some script =>
    if script matches .cons (.atom "blocked") _ then none else
    match action "sync_dir" script, namespaceSnapshot env with
    | some (success,error,mask,rest), some state =>
      if mask.size != 0 || (success && error != 0) then invalid else
      let updated := storeDirectory file directoryTypeName rest env
      if success then
        some (.ok (.Ok ()),storeNamespace {state with committed := state.names, pending := []} updated)
      else some (.ok (.Err ⟨error⟩),updated)
    | _,_ => invalid

/-- Directory destruction consumes the capability on either close outcome and
never supplies the namespace synchronization guarantee of fsync. -/
@[expose] def pollDirectoryClose (file : NativeFile) (env : Environment) :
    Option (Except Exception Unit × Environment) :=
  let invalid := some (.error .exhausted,env)
  match directoryHandle file env with
  | none => invalid
  | some script =>
    if script matches .cons (.atom "blocked") _ then none else
    match action "close_dir" script with
    | some (success,error,mask,rest) =>
      if mask.size != 0 || (success && error != 0) then invalid
      else some (.ok (),storeDirectory file closedDirectoryTypeName rest env)
    | _ => invalid

@[expose] def pollOpenReadOnly (path : Str) (env : Environment) :
    Option (Except Exception (core.result.Result NativeFile NativeIoError) × Environment) :=
  let invalid := some (.error .exhausted, env)
  let path := bytes path
  if !supportedOpenPath path then invalid else
  match namespaceState env with
  | none => invalid
  | some (names, script) =>
    if script matches .cons (.atom "blocked") _ then none else
    match openChoice path script with
    | none => invalid
    | some (success, error, ioScript, rest) =>
      if success then
        if error != 0 then invalid else
        if path.data == #[46] then
          let fresh := env.nativeRefCounter + 1
          if env.nativeHeap.any (fun cell => cell.1 == fresh) then invalid else
          let updated := replaceNamespaceScript rest env
          some (.ok (.Ok ⟨fresh⟩),{updated with
            nativeRefCounter := fresh
            nativeHeap := (fresh,directoryTypeName,.tuple #[ioScript]) :: updated.nativeHeap})
        else match names.filter (fun entry => entry.1.data == path.data) with
        | [(_, id)] =>
          match inode id env with
          | none => invalid
          | some _ =>
            let fresh := env.nativeRefCounter + 1
            if env.nativeHeap.any (fun cell => cell.1 == fresh) then invalid else
            let updated := replaceNamespaceScript rest env
            some (.ok (.Ok ⟨fresh⟩), {updated with
              nativeRefCounter := fresh
              nativeHeap := (fresh, handleTypeName, encodeHandle ⟨id,0,ioScript⟩) :: updated.nativeHeap})
        | _ => invalid
      else some (.ok (.Err ⟨error⟩), replaceNamespaceScript rest env)

@[expose] def openReadOnly (path : Str) : NativeM (core.result.Result NativeFile NativeIoError) :=
  .wait (pollOpenReadOnly path) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

@[expose] def lookup (file : NativeFile) (env : Environment) : Option State :=
  if file.id ≤ env.nativeRefCounter then
    match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
    | [(_, tag, contents)] => if tag == typeName then decode contents
      else if tag == handleTypeName || tag == writableHandleTypeName then sharedLookup file tag env else none
    | _ => none
  else none

@[expose] def store (file : NativeFile) (state : State) (env : Environment) : Environment :=
  match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
  | [(_, tag, contents)] =>
    if tag == typeName then
      {env with nativeHeap := env.nativeHeap.map fun cell =>
        if cell.1 == file.id then (file.id, typeName, encode state) else cell}
    else if tag == handleTypeName || tag == writableHandleTypeName then
      match decodeHandle contents with
      | some handle => sharedStore file handle state env
      | none => env
    else env
  | _ => env

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
    | some (reply, updated) =>
      match reply, getHandle file handleTypeName env with
      | .Ok _, some _ => some (.error .exhausted, env)
      | _, _ => some (.ok (reply, file), store file updated env)

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
  | none => pollDirectorySync file env
  | some state =>
    if blocked state then none else
    match syncStep state with
    | none => some (.error .exhausted, env)
    | some (reply, updated) => some (.ok reply, store file updated env)

@[expose] def syncAll (file : NativeFile) : NativeM (core.result.Result Unit NativeIoError) :=
  .wait (pollSync file) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- Model std::fs::File::set_len, including errors and blocking. Native file
and filesystem correspondence remain explicit OS assumptions. -/
@[expose] def pollSetLen (file : NativeFile) (length : U64) (env : Environment) :
    Option (Except Exception (core.result.Result Unit NativeIoError) × Environment) :=
  match lookup file env with
  | none => some (.error .exhausted, env)
  | some state =>
    if blocked state then none else
    match setLenStep state length with
    | none => some (.error .exhausted, env)
    | some (reply, updated) =>
      match reply, getHandle file handleTypeName env with
      | .Ok _, some _ => some (.error .exhausted, env)
      | _, _ => some (.ok reply, store file updated env)

@[expose] def setLen (file : NativeFile) (length : U64) : NativeM (core.result.Result Unit NativeIoError) :=
  .wait (pollSetLen file length) fun reply => match reply with
    | .ok value => .ok value
    | .error exception => .error exception

/-- File destruction consumes ownership even when the host close reports an error.
The retained image is ghost disk state, not a reusable descriptor. Close does not
acknowledge durability. Physical descriptor reclamation and std/OS/FFI behavior
remain explicit trusted boundaries. -/
@[expose] def closeStep (state : State) : Option State := do
  let (success, value, mask, rest) ← action "close" state.script
  if success && value != 0 then none else do
  let durable ← persist state.durable state.visible mask
  some {state with durable := durable, script := rest}

@[expose] def lookupClosed (file : NativeFile) (env : Environment) : Option State :=
  if file.id ≤ env.nativeRefCounter then
    match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
    | [(_, tag, contents)] => if tag == closedTypeName then decode contents
      else if tag == closedHandleTypeName then sharedLookup file closedHandleTypeName env else none
    | _ => none
  else none

@[expose] def retire (file : NativeFile) (state : State) (env : Environment) : Environment :=
  match env.nativeHeap.filter (fun cell => cell.1 == file.id) with
  | [(_, tag, contents)] =>
    if tag == typeName then
      {env with nativeHeap := env.nativeHeap.map fun cell =>
        if cell.1 == file.id then (file.id, closedTypeName, encode state) else cell}
    else if tag == handleTypeName || tag == writableHandleTypeName then
      match decodeHandle contents with
      | none => env
      | some handle =>
        let updated := sharedStore file handle state env
        {updated with nativeHeap := updated.nativeHeap.map fun cell =>
          if cell.1 == file.id then (file.id, closedHandleTypeName, cell.2.2) else cell}
    else env
  | _ => env

@[expose] def pollClose (file : NativeFile) (env : Environment) :
    Option (Except Exception Unit × Environment) :=
  match lookup file env with
  | none => pollDirectoryClose file env
  | some state =>
    if blocked state then none else
    match closeStep state with
    | none => some (.error .exhausted, env)
    | some updated => some (.ok (), retire file updated env)

@[expose] def close (file : NativeFile) : NativeM Unit :=
  .wait (pollClose file) fun reply => match reply with
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
  let state ← (lookup file env).orElse (fun _ => lookupClosed file env)
  let durable ← persist state.durable state.visible mask
  some ⟨durable, env.nativeRefCounter⟩

/-- Admit one newly opened, independent file into a fresh machine. This is an
explicit host/OS boundary, not a verified implementation of std::fs::File::open.
Old capabilities and all previous process/resource/lock state are discarded. -/
@[expose] def restart (image : Image) (script : Term) : Option (NativeFile × Environment) :=
  if image.bytes.size > limit then none else
    let file : NativeFile := ⟨image.highWater + 1⟩
    some (file, {
      nativeRefCounter := file.id
      nativeHeap := [(file.id, typeName, encode ⟨image.bytes, image.bytes, 0, script⟩)] })

/-- A bounded flat filesystem image. Capabilities, offsets, scripts, resource
owners and locks are volatile and are deliberately absent. -/
structure FilesystemImage where
  names : Names
  inodes : List (Nat × ByteArray)
  highWater : Nat

@[expose] def namedInode (names : Names) (path : ByteArray) : Option Nat :=
  (names.find? (fun entry => entry.1.data == path.data)).map (·.2)

/-- Unsynchronized path entries may persist independently, including partial
rename persistence. This overapproximates recorded metadata versions, rather than
assuming a filesystem persists an ordered prefix of directory operations. -/
@[expose] def namespaceCrashAllowed (state : NamespaceSnapshot) (chosen : Names) : Bool :=
  let versions := state.committed :: state.pending
  let known := versions.flatMap (fun names => names.map (·.1))
  chosen.all (fun entry => known.any (fun path => path.data == entry.1.data)) &&
    known.all (fun path => versions.any (fun names => namedInode names path == namedInode chosen path))

/-- Host crash admission chooses each inode's permitted byte image and each
pathname's recorded persistent version. Unknown names/inodes, duplicate choices,
unbounded images and malformed state are rejected. Filesystem metadata/data and
native descriptor correspondence remain explicit external model boundaries. -/
@[expose] def filesystemCrashImage (chosen : Names) (masks : List (Nat × ByteArray))
    (env : Environment) : Option FilesystemImage := do
  let state ← namespaceSnapshot env
  let names ← namespaceTable (encodeNames chosen)
  if !namespaceCrashAllowed state names then none else do
    let nodes := env.nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName)
    if nodes.length > 1024 || masks.map (·.1) != nodes.map (·.1) then none else do
      let images ← nodes.mapM fun cell => do
        let before ← inode cell.1 env
        let [(_,mask)] := masks.filter (fun choice => choice.1 == cell.1) | none
        let bytes ← persist before.durable before.visible mask
        some (cell.1,bytes)
      if names.any (fun entry => !(images.any (fun image => image.1 == entry.2))) then none
      else some ⟨names,images,env.nativeRefCounter⟩

/-- Restart preserves only admitted persistent names and bytes. Every old file,
directory, resource and lock capability is discarded; the high-water mark is
freshness bookkeeping and is not application disk data. -/
@[expose] def restartFilesystem (image : FilesystemImage) (script : Term) : Option Environment := do
  let names ← namespaceTable (encodeNames image.names)
  if image.inodes.length > 1024 ||
      (image.inodes.map (·.1)).eraseDups.length != image.inodes.length ||
      image.inodes.any (fun node => node.1 == 0 || node.1 > image.highWater || node.2.size > limit) ||
      names.any (fun entry => !(image.inodes.any (fun node => node.1 == entry.2))) then none
  else some {
    nativeRefCounter := image.highWater
    nativeHeap := (0,namespaceTypeName,encodeNamespace ⟨names,names,[],script⟩) ::
      image.inodes.map (fun (id,bytes) => (id,inodeTypeName,encode ⟨bytes,bytes,0,.nil⟩)) }

end NativeFile

instance : NativeDrop NativeFile where
  drop := NativeFile.close

instance : NativeOwnedDrop NativeFile where
  drop := NativeFile.close

namespace NativeMutex

/-- Consuming an unlocked mutex that owns a File runs file cleanup before
retiring the abstract mutex cell. Poisoning does not suppress destruction.
Raw mutex teardown, descriptor reclamation, std and OS correspondence remain
external boundaries. This is not a model for arbitrary payload destructors. -/
@[expose] def disposeFile (mutex : NativeMutex NativeFile) : NativeM Unit := do
  let contents ← NativeM.readCell (typeName NativeFile) mutex.id
  match contents with
  | .tuple fields =>
    if size : fields.size = 3 then
      let lockState := fields[0]'(by omega)
      let poisonState := fields[1]'(by omega)
      let payload := fields[2]'(by omega)
      if lockState == .atom "unlocked" &&
          (poisonState == .atom "unpoisoned" || poisonState == .atom "poisoned") then
        match NativeCodec.decode (α := NativeFile) payload with
        | some file => do
          NativeFile.close file
          let _ ← NativeM.removeCell (typeName NativeFile) mutex.id
          return ()
        | none => .error .exhausted
      else .error .exhausted
    else .error .exhausted
  | _ => .error .exhausted

/-- Compose ready File cleanup with removal of its owning mutex. The mutex
cell stays present during the close transition; all other cells are framed. -/
theorem disposeFile_next {α : Type} (mutex : NativeMutex NativeFile)
    (file : NativeFile) (poisoned : Bool) (env after : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, typeName NativeFile,
        .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
          NativeCodec.encode file])])
    (ready : NativeFile.pollClose file env = some (.ok (), after))
    (retained : after.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, typeName NativeFile,
        .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
          NativeCodec.encode file])])
    (next : Unit → NativeM α) :
    (disposeFile mutex >>= next) env =
      next () {after with nativeHeap := after.nativeHeap.filter (fun cell => cell.1 != mutex.id)} := by
  cases poisoned <;>
    simp [disposeFile, NativeM.readCell, stored, NativeCodec.roundtrip,
      NativeFile.close, Result.wait_bind, bind_assoc]
  all_goals
    try dsimp only
    rw [Result.wait_ready_run _ _ _ _ _ ready]
    simp [Result.ok_bind, NativeM.removeCell, retained]

end NativeMutex

instance (priority := 1100) : NativeOwnedDrop (NativeMutex NativeFile) where
  drop := NativeMutex.disposeFile

end Lynx
