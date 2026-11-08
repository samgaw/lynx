module

public import Lynx.Term

public section

namespace Lynx.Rustler

/-- Capabilities supplied by a validated, successfully loaded native library.
This models registration availability; native loader and FFI execution remain
trusted. Existing resource contents and other runtime state are preserved. -/
@[expose] def withResourceTypes {α : Type} (types : List String) (computation : Result α) :
    Result α := .nativeGet fun env =>
  .nativeSet { env with nativeResourceTypes := (env.nativeResourceTypes ++ types).eraseDups }
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

/-- Registration is a local get/set prefix of the actual generated adapter.
The following trace must hold for the resulting registry, rather than assuming
that every resource type was already available. -/
theorem withResourceTypes_registeredSteps {pid : PID} {computation : Result α}
    {before after : Nat × List (Nat × String × Term)} {value : α}
    (available types finalTypes : List String)
    (trace : Result.RegisteredSteps pid computation before
      (available ++ types).eraseDups value after finalTypes) :
    Result.RegisteredSteps pid (withResourceTypes types computation)
      before available value after finalTypes := by
  unfold withResourceTypes
  refine .update _ computation before before after available
    (available ++ types).eraseDups finalTypes value ?_ trace
  intro env _ refs heap registry
  congr 1
  cases env
  simp_all

/-- Registration remains local when the following decoder stops before a wait. -/
theorem withResourceTypes_registeredPrefix {pid : PID} {computation residual : Result α}
    {before after : Nat × List (Nat × String × Term)}
    (available types finalTypes : List String)
    (trace : Result.RegisteredPrefix pid computation before
      (available ++ types).eraseDups residual after finalTypes) :
    Result.RegisteredPrefix pid (withResourceTypes types computation)
      before available residual after finalTypes := by
  unfold withResourceTypes
  refine .update _ computation before before after available
    (available ++ types).eraseDups finalTypes residual ?_ trace
  intro env _ refs heap registry
  congr 1
  cases env
  simp_all

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

/-- The actual native prefix survives panic conversion and result encoding.
All state transitions remain those of the supplied computation. -/
theorem executeNative_readyPrefix {α : Type} {computation residual : Result α}
    {before after : Environment} (trace : Result.ReadyPrefix computation before residual after)
    (encode : α → Term) :
    Result.ReadyPrefix (executeNative computation encode) before (executeNative residual encode) after := by
  unfold executeNative
  exact (trace.bind _).handle _

/-- Local decoder/borrow steps retain the actual exception adapter at their
residual. A wait there is still interpreted by the scheduler. -/
theorem executeNative_registeredPrefix {α : Type} {pid : PID} {computation residual : Result α}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : Result.RegisteredPrefix pid computation before types residual after finalTypes)
    (encode : α → Term) :
    Result.RegisteredPrefix pid (executeNative computation encode) before types
      (executeNative residual encode) after finalTypes := by
  unfold executeNative
  exact (trace.bind _).handle _

/-- Preserve the actual exception adapter and encoder in a successful
scheduled native trace, including its local resource bookkeeping. -/
theorem executeNative_sharedSteps {α : Type} {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : Result.SharedSteps pid computation before value after) (encode : α → Term) :
    Result.SharedSteps pid (executeNative computation encode) before (encode value) after := by
  unfold executeNative
  exact (trace.bind (fun reply => Result.ok (encode reply)) (.done (encode value) after)).handle _

end Lynx.Rustler
