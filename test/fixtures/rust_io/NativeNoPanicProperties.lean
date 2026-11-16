module
public import Lynx
public import LockedAwait.NativeRuntime
public section
open Lynx
namespace LockedAwait.Safety

theorem panic_rejected : ¬ NativeM.NoPanic (NativeM.fail .panic : NativeM Unit) := by
  intro safe
  cases safe

@[expose] def blocked : NativeM Unit := .wait (fun _ => none) NativeM.ok

theorem blocked_is_exception_safe : NativeM.NoPanic blocked := by
  apply NativeM.NoPanic.wait
  intro env reply after impossible
  cases impossible

theorem blocked_is_not_success :
    Concurrent.checkPost (fun config => match config.outcome with | .ok _ => true | _ => false) 8 (.start {} blocked) = false := by
  cbv

/-- A preceding store does not justify assuming no interference at a later
shared-state read. NoPanic checks that continuation for every environment. -/
@[expose] def unsafeReadAfterWrite : NativeM Unit :=
  .nativeSet {} (.nativeGet fun env =>
    if env.nativeRefCounter == 0 then NativeM.ok () else NativeM.fail .panic)

theorem interference_is_not_assumed_away : ¬ NativeM.NoPanic unsafeReadAfterWrite := by
  intro safe
  cases safe with
  | nativeSet _ _ tail =>
    cases tail with
    | nativeGet _ all =>
      have bad := all {nativeRefCounter := 1}
      simp only [show ((1 : Nat) == 0) = false from rfl, Bool.false_eq_true, ↓reduceIte] at bad
      cases bad

end LockedAwait.Safety
