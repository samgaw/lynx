module

public import Lynx.Term

public section

namespace Lynx.Rustler

/-- Capabilities supplied by a validated, successfully loaded native library.
This models registration availability; native loader and FFI execution remain
trusted. Existing resource contents and other runtime state are preserved. -/
@[expose] def withResourceTypes {α : Type} (types : List String) (computation : Result α) :
    Result α := .get fun env =>
  .set { env with nativeResourceTypes := (env.nativeResourceTypes ++ types).eraseDups }
    computation

@[simp] theorem withResourceTypes_apply {α : Type} (types : List String)
    (computation : Result α) (env : Environment) :
    withResourceTypes types computation env =
      computation { env with nativeResourceTypes := (env.nativeResourceTypes ++ types).eraseDups } := by
  simp [withResourceTypes]

theorem registered_resource_type (types : List String) (env : Environment)
    (name : String) (member : name ∈ types) :
    name ∈ (env.nativeResourceTypes ++ types).eraseDups := by
  simp [member]

/-- Rustler 0.38/0.39 accept only the atoms `true` and `false` as booleans. -/
@[expose] def decodeBool : Term → Except Exception Bool
  | .atom "true" => .ok true
  | .atom "false" => .ok false
  | _ => .error (.error (.atom "badarg"))

/-- Rustler encodes booleans as the corresponding Erlang atoms. -/
@[expose] def encodeBool (value : Bool) : Term :=
  if value then .atom "true" else .atom "false"

@[simp] theorem decodeBool_encodeBool (value : Bool) :
    decodeBool (encodeBool value) = .ok value := by
  cases value <;> rfl

/-- Convert the modeled Rust panic after executing a resumable native body.
State changes and blocking waits remain in the surrounding Lynx runtime;
verification exhaustion cannot be caught as a native exception. -/
@[expose] def executeNative {α : Type} (computation : Result α) (encode : α → Term) : Result Term :=
  Result.handle (do let value ← computation; .ok (encode value)) fun error =>
    match error with
    | .error (.atom "rust_panicked") => .error (.error (.atom "nif_panicked"))
    | _ => .error .exhausted

@[simp] theorem executeNative_ok {α : Type} (value : α) (encode : α → Term) :
    executeNative (.ok value) encode = .ok (encode value) := rfl

@[simp] theorem executeNative_panic {α : Type} (encode : α → Term) :
    executeNative (.error (.error (.atom "rust_panicked")) : Result α) encode =
      .error (.error (.atom "nif_panicked")) := rfl

@[simp] theorem executeNative_exhausted {α : Type} (encode : α → Term) :
    executeNative (.error .exhausted : Result α) encode = .error .exhausted := rfl

/-- Native state polls execute in the same environment as the caller. -/
theorem executeNative_wait {α β : Type} (poll : Environment → Option (β × Environment))
    (next : β → Result α) (encode : α → Term) :
    executeNative (.wait poll next) encode =
      .wait poll (fun value => executeNative (next value) encode) := rfl

end Lynx.Rustler
