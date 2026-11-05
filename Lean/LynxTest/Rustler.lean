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

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Rustler
  LynxTest.ProofAudit.checkModule `LynxTest.Rustler

end LynxTest.Rustler
