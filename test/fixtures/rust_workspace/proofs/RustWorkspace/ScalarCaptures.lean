module
public import ScalarCapture.Extraction.Funs
public import ScalarCapture.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace ScalarCapture.Properties

theorem core_spec (input : core.result.Result U64 U64) (mask : U64) :
    experiment_nif.experiment_core.mask_error input mask = RustM.ok
      (match input with | .Ok value => .Ok value | .Err error => .Err (error ^^^ mask)) := by
  cases input <;> simp [experiment_nif.experiment_core.mask_error, core.result.Result.map_err,
    experiment_nif.experiment_core.mask_error.closure.Insts.CoreOpsFunctionFnOnceTupleU64U64.call_once]

theorem caller_spec (value mask : U64) :
    experiment_nif.experiment_analysis.masked_error value mask = RustM.ok (.Err (value ^^^ mask)) := by
  simp [experiment_nif.experiment_analysis.masked_error, core_spec]

theorem facade_spec (value mask : U64) :
    __FACADE__ value mask = RustM.ok (.Err (value ^^^ mask)) := by
  simpa [__FACADE__] using caller_spec value mask

theorem zero_spec (value : U64) :
    __FACADE__ value 0#u64 = RustM.ok (.Err value) := by
  have eq : value ^^^ (0#u64) = value := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simp
  simp [facade_spec, eq]

theorem self_spec (value : U64) :
    __FACADE__ value value = RustM.ok (.Err 0#u64) := by
  have eq : value ^^^ value = (0#u64) := by
    apply (UScalar.eq_equiv_bv_eq _ _).mpr
    simp
  simp [facade_spec, eq]

end ScalarCapture.Properties
