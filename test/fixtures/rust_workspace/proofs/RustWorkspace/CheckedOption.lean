module
public import RustWorkspace.CheckedFacade.Funs
public import RustWorkspace.CheckedInternal
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.CheckedOption

/-- A kernel-checked correspondence between the two actual extraction units. -/
theorem link_spec (value : I64) :
    experiment_nif.experiment_analysis.analyse value = experiment_analysis.analyse value := by
  simp only [experiment_nif.experiment_analysis.analyse, experiment_analysis.analyse,
    experiment_nif.experiment_core.evaluate, experiment_analysis.experiment_core.evaluate]
  rfl

theorem output_spec (value : I64) :
    ∃ result, experiment_nif.experiment_analysis.analyse value = RustM.ok result ∧
      match result with
      | none => ¬ (-4611686018427387904 ≤ value.val ∧ value.val < 4611686018427387904)
      | some output => -4611686018427387904 ≤ value.val ∧ value.val < 4611686018427387904 ∧
          output.val = 2 * value.val + 1 := by
  rw [link_spec]
  exact CheckedInternal.output_spec value

theorem facade_spec (value : I64) :
    ∃ result,
      experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.checked_analyse value = RustM.ok result ∧
      match result with
      | none => ¬ (-4611686018427387904 ≤ value.val ∧ value.val < 4611686018427387904)
      | some output => -4611686018427387904 ≤ value.val ∧ value.val < 4611686018427387904 ∧
          output.val = 2 * value.val + 1 := by
  exact output_spec value

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.CheckedFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.CheckedOption

end RustWorkspace.CheckedOption
