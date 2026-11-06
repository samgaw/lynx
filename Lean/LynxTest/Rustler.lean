import LynxTest.ProofAudit
import Lynx.Rustler

namespace LynxTest.Rustler

theorem boolRoundtrip (value : Bool) :
    Lynx.Rustler.decodeBool (Lynx.Rustler.encodeBool value) = .ok value :=
  Lynx.Rustler.decodeBool_encodeBool value

theorem integerIsNotBool (value : Int) :
    Lynx.Rustler.decodeBool (.integer value) = .error (.error (.atom "badarg")) := rfl

theorem otherAtomIsNotBool (name : String) (ht : name ≠ "true") (hf : name ≠ "false") :
    Lynx.Rustler.decodeBool (.atom name) = .error (.error (.atom "badarg")) := by
  simp [Lynx.Rustler.decodeBool, ht, hf]

/-- A native panic does not undo effects performed before the failure. -/
theorem nativePanicPreservesState (env updated : Lynx.Environment) :
    Lynx.Rustler.executeNative
      (Lynx.Result.set updated (.error (.error (.atom "rust_panicked"))) : Lynx.Result Lynx.Term)
      id env = (.error (.error (.atom "nif_panicked")), updated) := by
  simp [Lynx.Rustler.executeNative, Lynx.Result.handle]

/-- Unsupported native exceptions cannot become successful or catchable results. -/
theorem unsupportedNativeException :
    Lynx.Rustler.executeNative (.error (.throw .nil) : Lynx.Result Lynx.Term) id =
      .error .exhausted := rfl

/-- Blocking polls and their updates remain in the caller's runtime. -/
theorem nativeWaitPanic (poll : Lynx.Environment → Option (Unit × Lynx.Environment))
    (env updated : Lynx.Environment) (ready : poll env = some ((), updated)) :
    Lynx.Rustler.executeNative
      (.wait poll (fun _ => .error (.error (.atom "rust_panicked"))) : Lynx.Result Lynx.Term)
      id env = (.error (.error (.atom "nif_panicked")), updated) := by
  rw [Lynx.Rustler.executeNative_wait]
  rw [Lynx.Result.wait_ready_apply _ _ _ _ _ ready]
  rfl

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Rustler
  LynxTest.ProofAudit.checkModule `LynxTest.Rustler

end LynxTest.Rustler
