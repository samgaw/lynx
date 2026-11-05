module

public import RustWorkspace.Extraction.Funs
public meta import LynxTest.ProofAudit

open Aeneas Aeneas.Std

public section

namespace RustWorkspace

/-- A property of the extracted internal Rust function, independent of NIF exposure. -/
theorem invert_spec (value : Bool) :
    experiment_analysis.experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

/-- Composition uses the proven dependency result and the extracted caller body. -/
theorem restore_spec (value : Bool) :
    experiment_analysis.restore value = RustM.ok value := by
  simp only [experiment_analysis.restore, invert_spec, bind_ok]
  cases value <;> rfl

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.Extraction.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.Composition

end RustWorkspace
