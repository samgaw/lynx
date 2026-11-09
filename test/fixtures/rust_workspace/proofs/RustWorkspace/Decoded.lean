module
public import Decoded.Extraction.Funs
public import Decoded.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace Decoded.Properties

theorem invert_spec (value : Bool) : experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem restore_spec (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
  cases value <;> simp [experiment_analysis.restore, invert_spec]

theorem decoder_success (input : Lynx.Term) (value : U64)
    (decoded : Lynx.Rustler.decodeUnsigned .U64 64 input = .ok value) :
    __DECODER__ input = RustM.ok (.Ok { enabled := value != 0#u64 }) := by
  simp [__DECODER__, Lynx.Rustler.Decoding.u64, decoded]

theorem decoder_error (input : Lynx.Term) (error : Lynx.Exception)
    (rejected : Lynx.Rustler.decodeUnsigned .U64 64 input = .error error) :
    __DECODER__ input = RustM.ok (.Err (.error error)) := by
  simp [__DECODER__, Lynx.Rustler.Decoding.u64, rejected]

theorem decoder_range (value : Int) (outside : ¬ (0 ≤ value ∧ value < 2^64)) :
    __DECODER__ (.integer value) = RustM.ok (.Err (.error (.error (.atom "badarg")))) := by
  exact decoder_error (.integer value) _
    (Lynx.Rustler.decodeUnsigned_outOfRange .U64 64 value outside)

theorem facade_spec (input : ProtocolFlag) (shouldPanic : Bool) :
    __IMPLEMENTATION__ input shouldPanic =
      if shouldPanic then RustM.fail .panic else RustM.ok input.enabled := by
  cases shouldPanic <;> simp [__IMPLEMENTATION__, restore_spec]

end Decoded.Properties
