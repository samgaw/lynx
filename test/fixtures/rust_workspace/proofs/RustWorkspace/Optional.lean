module
public import RustWorkspace.OptionalFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.Optional

@[expose] def policy : Option Bool → Bool
  | some flag => !flag
  | none => false

theorem core_spec (value : Option Bool) :
    experiment_nif.experiment_core.optional_flag value = RustM.ok (policy value) := by
  cases value <;> rfl

theorem caller_spec (value : Option Bool) :
    experiment_nif.experiment_analysis.optional_flag value = RustM.ok (policy value) :=
  core_spec value

theorem nested_nil_is_some_none :
    Lynx.Rustler.decodeOption (Lynx.Rustler.decodeOption Lynx.Rustler.decodeBool)
      (.atom "nil") = .ok (some none) := rfl

theorem nested_encoding_collision :
    Lynx.Rustler.encodeOption (Lynx.Rustler.encodeOption Lynx.Rustler.encodeBool) none =
    Lynx.Rustler.encodeOption (Lynx.Rustler.encodeOption Lynx.Rustler.encodeBool) (some none) := rfl

theorem optional_badarg :
    Lynx.Rustler.decodeOption Lynx.Rustler.decodeBool (.integer 1) =
      .error (.error (.atom "badarg")) := rfl

theorem optional_panic (value : U8) (tail : Int) :
    Lynx.Rustler.decodeOption Lynx.Rustler.decodeByteVec
      (.cons (Lynx.Rustler.encodeUnsigned value) (.integer tail)) =
      .error (.error (.atom "nif_panicked")) :=
  Lynx.Rustler.decodeOption_panic _ _ (Lynx.Rustler.decodeByteVec_improper value tail)

theorem optional_exhaustion (input : Lynx.Term)
    (h : Lynx.Rustler.decodeByteVec input = .error .exhausted) :
    Lynx.Rustler.decodeOption Lynx.Rustler.decodeByteVec input = .error .exhausted := by
  simp [Lynx.Rustler.decodeOption, h]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.OptionalFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.Optional
end RustWorkspace.Optional
