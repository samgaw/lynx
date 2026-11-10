module
public import Returned.Extraction.Funs
public import Returned.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace Returned.Properties

theorem invert_spec (value : Bool) : experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem restore_spec (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
  cases value <;> simp [experiment_analysis.restore, invert_spec]

theorem success (input : Lynx.Term) (value : U64) (shouldPanic : Bool)
    (decoded : Lynx.Rustler.decodeUnsigned .U64 64 input = .ok value) :
    experiment_nif.decode_result_impl input shouldPanic =
      if shouldPanic then RustM.fail .panic else RustM.ok (.Ok (value != 0#u64)) := by
  cases shouldPanic <;>
    simp [experiment_nif.decode_result_impl, Lynx.Rustler.Decoding.u64, decoded, restore_spec]

theorem rejected (input : Lynx.Term) (error : Lynx.Exception) (shouldPanic : Bool)
    (failed : Lynx.Rustler.decodeUnsigned .U64 64 input = .error error) :
    experiment_nif.decode_result_impl input shouldPanic = RustM.ok (.Err (.error error)) := by
  simp [experiment_nif.decode_result_impl, Lynx.Rustler.Decoding.u64, failed]

theorem rejected_range (value : Int) (shouldPanic : Bool)
    (outside : ¬ (0 ≤ value ∧ value < 2^64)) :
    experiment_nif.decode_result_impl (.integer value) shouldPanic =
      RustM.ok (.Err (.error (.error (.atom "badarg")))) := by
  exact rejected _ _ _ (Lynx.Rustler.decodeUnsigned_outOfRange .U64 64 value outside)

theorem aliased_spec (input : Lynx.Term) (shouldPanic : Bool) :
    __ALIASED__ input shouldPanic = experiment_nif.decode_result_impl input shouldPanic := by
  simp [__ALIASED__]

theorem spelled_spec (input : Lynx.Term) (shouldPanic : Bool) :
    __SPELLED__ input shouldPanic = experiment_nif.decode_result_impl input shouldPanic := by
  simp [__SPELLED__]

theorem identity_spec (input : Lynx.Term) : __IDENTITY__ input = RustM.ok input := by
  rfl

end Returned.Properties
