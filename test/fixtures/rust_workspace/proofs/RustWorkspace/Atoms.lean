module
public import Atoms.Extraction.Funs
public import Atoms.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace Atoms.Properties

theorem invert_spec (value : Bool) : experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem restore_spec (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
  cases value <;> simp [experiment_analysis.restore, invert_spec]

theorem validation_spec (input : Lynx.Term) (value : U64)
    (decoded : Lynx.Rustler.decodeUnsigned .U64 64 input = .ok value) :
    experiment_nif.validate_nonzero input = RustM.ok
      (if value = 0#u64 then .Err __ATOM__ else .Ok (value != 0#u64)) := by
  by_cases zero : value = 0#u64 <;>
    simp [experiment_nif.validate_nonzero, Lynx.Rustler.Decoding.u64, decoded, zero, restore_spec]

theorem validation_error (input : Lynx.Term) (error : Lynx.Exception)
    (rejected : Lynx.Rustler.decodeUnsigned .U64 64 input = .error error) :
    experiment_nif.validate_nonzero input = RustM.ok (.Err (.error error)) := by
  simp [experiment_nif.validate_nonzero, Lynx.Rustler.Decoding.u64, rejected]

theorem raising_spec (input : Lynx.Term) (value : U64)
    (decoded : Lynx.Rustler.decodeUnsigned .U64 64 input = .ok value) :
    experiment_nif.raise_nonzero input = RustM.ok
      (if value = 0#u64 then .Err __RAISE__ else .Ok (value != 0#u64)) := by
  by_cases zero : value = 0#u64 <;>
    simp [experiment_nif.raise_nonzero, Lynx.Rustler.Decoding.u64, decoded, zero, restore_spec]

theorem raising_error (input : Lynx.Term) (error : Lynx.Exception)
    (rejected : Lynx.Rustler.decodeUnsigned .U64 64 input = .error error) :
    experiment_nif.raise_nonzero input = RustM.ok (.Err (.error error)) := by
  simp [experiment_nif.raise_nonzero, Lynx.Rustler.Decoding.u64, rejected]

theorem decoder_spec (input : Lynx.Term) :
    __DECODER__ input = (do
      let result ← experiment_nif.validate_nonzero input
      match result with
      | .Ok enabled => RustM.ok (.Ok { enabled := enabled })
      | .Err error => RustM.ok (.Err error)) := by rfl

theorem flag_spec (input : ValidatedFlag) : __FLAG__ input = RustM.ok input.enabled := by
  simp [__FLAG__, restore_spec]

theorem result_spec (input : Lynx.Term) : __RESULT__ input = experiment_nif.raise_nonzero input := by
  simp [__RESULT__]

theorem zero_rejected : experiment_nif.validate_nonzero (.integer 0) =
    RustM.ok (.Err (.ok (.atom "zero"))) := by
  have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok 0#u64 := by
    have encoded : Lynx.Rustler.encodeUnsigned (0#u64) = .integer 0 := by simp [Lynx.Rustler.encodeUnsigned]
    rw [← encoded]
    exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 0#u64
  simpa [__ATOM__, Lynx.Rustler.atomErrorOutcome] using validation_spec (.integer 0) 0#u64 decoded

theorem zero_raised : experiment_nif.raise_nonzero (.integer 0) =
    RustM.ok (.Err (.error (.error (.atom "zero")))) := by
  have decoded : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok 0#u64 := by
    have encoded : Lynx.Rustler.encodeUnsigned (0#u64) = .integer 0 := by simp [Lynx.Rustler.encodeUnsigned]
    rw [← encoded]
    exact Lynx.Rustler.decodeUnsigned_encodeUnsigned 0#u64
  simpa [__RAISE__, Lynx.Rustler.raiseAtomErrorOutcome] using raising_spec (.integer 0) 0#u64 decoded

end Atoms.Properties
