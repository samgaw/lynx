module
public import Aeneas
public section

namespace __OPTION_NAMESPACE__
open Aeneas Aeneas.Std

/-- Option::and_then for an audited capture-free callback with NoopDestruct.
    The callback dictionary is its actual extracted implementation. -/
@[expose] def andThen {T U F : Type}
    (fnOnce : core.ops.function.FnOnce F T (Option U))
    (input : Option T) (callback : F) : RustM (Option U) :=
  match input with
  | none => RustM.ok none
  | some value => fnOnce.call_once callback value

@[simp] theorem andThen_none {T U F : Type}
    (fnOnce : core.ops.function.FnOnce F T (Option U)) (callback : F) :
    andThen fnOnce none callback = RustM.ok none := rfl

@[simp] theorem andThen_some {T U F : Type}
    (fnOnce : core.ops.function.FnOnce F T (Option U)) (value : T) (callback : F) :
    andThen fnOnce (some value) callback = fnOnce.call_once callback value := rfl
end __OPTION_NAMESPACE__
