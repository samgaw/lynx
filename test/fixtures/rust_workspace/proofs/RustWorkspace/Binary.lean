module

public import RustWorkspace.BinaryFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit

open Aeneas Aeneas.Std

public section
namespace RustWorkspace.Binary

theorem core_spec {T : Type} (value : T) :
    experiment_nif.experiment_core.preserve value = RustM.ok value := rfl

theorem composition {T : Type} (value : T) :
    experiment_nif.experiment_analysis.preserve value = RustM.ok value := core_spec value

theorem facade_spec (value : Lynx.Rustler.Binary) :
    experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.echo_binary value =
      RustM.ok value := composition value

theorem core_length_spec (value : Slice U8) :
    ∃ count, experiment_nif.experiment_core.byte_length value = RustM.ok count ∧
      count.val = value.val.length := by
  refine ⟨_, rfl, ?_⟩
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  · simp
  · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

theorem length_composition (value : Slice U8) :
    ∃ count, experiment_nif.experiment_analysis.byte_length value = RustM.ok count ∧
      count.val = value.val.length := core_length_spec value

theorem length_facade_spec (value : Lynx.Rustler.Binary)
    (unsignedBound : value.size ≤ Usize.max) (signedBound : value.size ≤ Isize.max.toNat) :
    ∃ count,
      experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.binary_length value =
        RustM.ok count ∧ count.val = value.size := by
  obtain ⟨slice, decoded, size⟩ := Lynx.Rustler.binaryAsSlice_spec value unsignedBound signedBound
  obtain ⟨count, computed, countSize⟩ := length_composition slice
  refine ⟨count, ?_, countSize.trans size⟩
  simp [experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.binary_length,
    decoded, computed]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.BinaryFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.Binary

end RustWorkspace.Binary
