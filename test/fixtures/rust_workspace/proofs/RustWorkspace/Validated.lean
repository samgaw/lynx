module
public import Validated.Extraction.Funs
public import Validated.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace Validated.Properties

theorem invert_spec (value : Bool) : experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem restore_spec (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
  cases value <;> simp [experiment_analysis.restore, invert_spec]

theorem validation_spec (input : Lynx.Term) (value : U64)
    (decoded : Lynx.Rustler.decodeUnsigned .U64 64 input = .ok value) :
    experiment_nif.validate_nonzero input = RustM.ok
      (if value = 0#u64 then .Err Lynx.Rustler.badArgOutcome else .Ok (value != 0#u64)) := by
  by_cases zero : value = 0#u64 <;>
    simp [experiment_nif.validate_nonzero, Lynx.Rustler.Decoding.u64, decoded, zero, restore_spec, Lynx.Rustler.Decoding.dropScalarResult]

theorem validation_error (input : Lynx.Term) (error : Lynx.Exception)
    (rejected : Lynx.Rustler.decodeUnsigned .U64 64 input = .error error) :
    experiment_nif.validate_nonzero input = RustM.ok (.Err (.error error)) := by
  have kind := Lynx.Rustler.decodeUnsigned_error rejected
  subst error
  simp [experiment_nif.validate_nonzero, Lynx.Rustler.Decoding.u64, rejected,
    Lynx.Rustler.Decoding.dropScalarResult, Lynx.Rustler.badArgOutcome,
    Lynx.Rustler.Decoding.dropDecoderError]

theorem decoder_spec (input : Lynx.Term) :
    __DECODER__ input = (do
      let result ← experiment_nif.validate_nonzero input
      match result with
      | .Ok enabled => RustM.ok (.Ok { enabled := enabled })
      | .Err error => RustM.ok (.Err error)) := by
  cases decoded : Lynx.Rustler.decodeUnsigned .U64 64 input with
  | ok value =>
    have validated := validation_spec input value decoded
    by_cases zero : value = 0#u64 <;>
      simp [__DECODER__, validated, zero, Lynx.Rustler.Decoding.dropScalarResult,
        Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome]
  | error error =>
    have kind := Lynx.Rustler.decodeUnsigned_error decoded
    have validated := validation_error input error decoded
    subst error
    simp [__DECODER__, validated, Lynx.Rustler.Decoding.dropScalarResult,
      Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome]

theorem flag_spec (input : ValidatedFlag) : __FLAG__ input = RustM.ok input.enabled := by
  simp [__FLAG__, restore_spec]

theorem result_spec (input : Lynx.Term) : __RESULT__ input = experiment_nif.validate_nonzero input := by
  simp [__RESULT__]

theorem zero_rejected : experiment_nif.validate_nonzero (.integer 0) =
    RustM.ok (.Err (.error (.error (.atom "badarg")))) := by
  have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok 0#u64 := by
    have encoded : Lynx.Rustler.encodeUnsigned (0#u64) = .integer 0 := by simp [Lynx.Rustler.encodeUnsigned]
    rw [← encoded]
    exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 0#u64
  simpa [Lynx.Rustler.badArgOutcome] using validation_spec (.integer 0) 0#u64 decoded

end Validated.Properties
