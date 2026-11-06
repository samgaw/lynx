module

public import Aeneas
public import Lynx.Term

/-! Interpretation of extracted native computations in Lynx's resumable runtime.
A native panic is retained as the `rust_panicked` marker. It must be converted by
a native facade before becoming an Elixir-visible exception. Undefined behavior
and divergence are verification exhaustion, never successful native returns.
This module does not add resource, lock, executor or FFI models. -/

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
