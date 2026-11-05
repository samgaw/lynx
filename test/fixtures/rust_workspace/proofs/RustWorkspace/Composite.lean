module

public import RustWorkspace.CompositeFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit

open Aeneas Aeneas.Std

public section
namespace RustWorkspace.Composite

theorem decide_spec (reading : experiment_nif.experiment_core.Reading) :
    experiment_nif.experiment_core.decide reading = RustM.ok
      (if reading.enabled then experiment_nif.experiment_core.Decision.Accept reading.value
        else experiment_nif.experiment_core.Decision.Reject 7#u8) := by
  unfold experiment_nif.experiment_core.decide
  split <;> rfl

theorem classify_spec (flag : Bool) (value : I64) :
    experiment_nif.experiment_analysis.classify (flag, value) = RustM.ok
      (if flag then core.result.Result.Ok value else core.result.Result.Err 7#u8) := by
  cases flag <;> simp [experiment_nif.experiment_analysis.classify, decide_spec, bind_ok]

theorem classify_facade (flag : Bool) (value : I64) :
    experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.classify (flag, value) = RustM.ok
      (if flag then core.result.Result.Ok value else core.result.Result.Err 7#u8) :=
  classify_spec flag value

theorem tuple_core (flag : Bool) (value : I64) :
    experiment_nif.experiment_core.transform_pair (flag, value) = RustM.ok (!flag, value) := by
  rfl

theorem tuple_composition (flag : Bool) (value : I64) :
    experiment_nif.experiment_analysis.transform_pair (flag, value) = RustM.ok (!flag, value) :=
  tuple_core flag value

theorem tuple_facade (flag : Bool) (value : I64) :
    experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.transform_pair (flag, value) =
      RustM.ok (!flag, value) := tuple_composition flag value

theorem reverse_result_ok (value : I64) :
    experiment_nif.__12.__INVENTORY.nif_func.wrapper.closure.reverse_result (.Ok value) =
      RustM.ok (.Err value) := rfl

theorem reverse_result_err (value : U8) :
    experiment_nif.__12.__INVENTORY.nif_func.wrapper.closure.reverse_result (.Err value) =
      RustM.ok (.Ok value) := rfl

theorem nested_identity (value : Bool × (U8 × I64 × Unit)) :
    experiment_nif.__13.__INVENTORY.nif_func.wrapper.closure.echo_nested value =
      RustM.ok value := rfl

theorem seven_identity (value : U8 × U8 × U8 × U8 × U8 × U8 × U8) :
    experiment_nif.__14.__INVENTORY.nif_func.wrapper.closure.echo_seven value =
      RustM.ok value := rfl

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.CompositeFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.Composite

end RustWorkspace.Composite
