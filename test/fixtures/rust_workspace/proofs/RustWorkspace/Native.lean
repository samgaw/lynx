module

public import RustWorkspace.Facade.Funs
public import Lynx.Rustler
public meta import LynxTest.ProofAudit

open Aeneas Aeneas.Std

public section
namespace RustWorkspace.Native

-- These proofs concern the bodies extracted together from the compiled facade.
theorem invert_spec (value : Bool) :
    experiment_nif.experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem analysis_spec (value : Bool) :
    experiment_nif.experiment_analysis.restore value = RustM.ok value := by
  simp only [experiment_nif.experiment_analysis.restore, invert_spec, bind_ok]
  cases value <;> rfl

theorem facade_spec (value : Bool) :
    experiment_nif.«_».__INVENTORY.nif_func.wrapper.closure.native_restore value =
      RustM.ok value := analysis_spec value

theorem negate_spec (value : Bool) :
    experiment_nif.__1.__INVENTORY.nif_func.wrapper.closure.negate value = RustM.ok (!value) := by
  simp [experiment_nif.__1.__INVENTORY.nif_func.wrapper.closure.negate, analysis_spec, bind_ok]

-- The internal integer function is not a NIF. Its caller reuses this theorem.
theorem double_spec (value : I64)
    (hlo : -4611686018427387904 ≤ value.val)
    (hhi : value.val ≤ 4611686018427387903) :
    experiment_nif.experiment_core.double value ⦃ result => result.val = value.val * 2 ⦄ := by
  unfold experiment_nif.experiment_core.double
  apply IScalar.mul_spec <;> scalar_tac

theorem integer_composition (value : I64)
    (hlo : -4611686018427387904 ≤ value.val)
    (hhi : value.val ≤ 4611686018427387903) :
    experiment_nif.experiment_analysis.twice_plus_one value
      ⦃ result => result.val = value.val * 2 + 1 ⦄ := by
  unfold experiment_nif.experiment_analysis.twice_plus_one
  apply WP.spec_bind (double_spec value hlo hhi)
  intro doubled hd
  apply WP.spec_mono (IScalar.add_bv_spec (x := doubled) (y := 1#i64) ?_ ?_)
  · intro result hresult
    simpa [hd] using hresult.1
  · scalar_tac
  · scalar_tac

theorem integer_facade (value : I64)
    (hlo : -4611686018427387904 ≤ value.val)
    (hhi : value.val ≤ 4611686018427387903) :
    experiment_nif.__2.__INVENTORY.nif_func.wrapper.closure.calculate value
      ⦃ result => result.val = value.val * 2 + 1 ⦄ :=
  integer_composition value hlo hhi

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.Facade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.Native

end RustWorkspace.Native
