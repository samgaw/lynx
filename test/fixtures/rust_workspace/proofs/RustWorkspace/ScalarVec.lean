module
public import RustWorkspace.ScalarFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std experiment_nif.experiment_analysis
namespace RustWorkspace.ScalarVec

theorem slice_transition (input : Slice I64) (value : I64) :
    experiment_nif.experiment_core.collections.replace_slice_first_i64 input value =
      RustM.ok (!input.val.isEmpty, input.set 0#usize value) := by
  cases shape : input.val with
  | nil =>
    have unchanged : input.set 0#usize value = input := by
      apply Slice.ext
      simp [Slice.set_val_eq, shape]
    simp [experiment_nif.experiment_core.collections.replace_slice_first_i64, core.slice.Slice.is_empty,
      shape, unchanged]
  | cons old tail =>
    simp [experiment_nif.experiment_core.collections.replace_slice_first_i64, core.slice.Slice.is_empty,
      shape, Slice.update, Slice.set, Slice.setAtNat]

theorem vector_transition (input : alloc.vec.Vec I64) (value : I64) :
    experiment_nif.experiment_core.collections.replace_first_i64 input value =
      RustM.ok (!input.val.isEmpty, ⟨input.slice.set 0#usize value⟩) := by
  simp [experiment_nif.experiment_core.collections.replace_first_i64, alloc.vec.Vec.deref_mut, lift,
    slice_transition, alloc.vec.Vec.val]

theorem composition (input : alloc.vec.Vec I64) (value : I64) :
    replace_first_i64 input value =
      RustM.ok (!input.val.isEmpty, ⟨input.slice.set 0#usize value⟩) := by
  exact vector_transition input value

theorem preserves_length (input : alloc.vec.Vec I64) (value : I64) :
    ∃ changed updated, replace_first_i64 input value = RustM.ok (changed, updated) ∧
      updated.val = input.val.set 0 value ∧ updated.val.length = input.val.length := by
  refine ⟨_, _, composition input value, ?_, ?_⟩
  · simp [alloc.vec.Vec.val, Slice.set_val_eq]
  · simp [alloc.vec.Vec.val, Slice.set_val_eq]

theorem empty_unchanged (input : alloc.vec.Vec I64) (value : I64)
    (empty : input.val = []) :
    replace_first_i64 input value = RustM.ok (false, input) := by
  rw [composition]
  have emptySlice : input.slice.val = [] := empty
  have unchanged : (⟨input.slice.set 0#usize value⟩ : alloc.vec.Vec I64) = input := by
    apply alloc.vec.Vec.ext
    simp only [alloc.vec.Vec.val, Slice.set_val_eq]
    rw [emptySlice]
    rfl
  simp [empty, unchanged]

theorem facade_spec (input : alloc.vec.Vec I64) (value : I64) :
    experiment_nif.__10.__INVENTORY.nif_func.wrapper.closure.replace_first_i64 input value =
      RustM.ok (!input.val.isEmpty, ⟨input.slice.set 0#usize value⟩) := composition input value

@[expose] def inputVector : alloc.vec.Vec I64 :=
  alloc.vec.Vec.from [(-1)#i64, 42#i64] (by simp; scalar_tac)

theorem input_decoded : Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64)
    (Lynx.Term.list [.integer (-1), .integer 42]) = .ok inputVector := by
  unfold inputVector
  apply Lynx.Rustler.decodeScalarVec_values _ ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) (.cons (by rfl) .nil)

@[expose] def flagsVector : alloc.vec.Vec Bool := alloc.vec.Vec.from [true, false] (by simp; scalar_tac)
theorem flags_decoded : Lynx.Rustler.decodeScalarVec Lynx.Rustler.decodeBool
    (Lynx.Term.list [.atom "true", .atom "false"]) = .ok flagsVector := by
  unfold flagsVector
  apply Lynx.Rustler.decodeScalarVec_values _ ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) (.cons (by rfl) .nil)

@[expose] def signedVector : alloc.vec.Vec I8 := alloc.vec.Vec.from [(-128)#i8] (by simp; scalar_tac)
theorem signed_decoded : Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I8 32)
    (Lynx.Term.list [.integer 128]) = .ok signedVector := by
  unfold signedVector
  apply Lynx.Rustler.decodeScalarVec_values _ ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) .nil

theorem flags_head_error (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec Lynx.Rustler.decodeBool (.cons (.integer 1) tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem flags_improper (tail : Int) :
    Lynx.Rustler.decodeScalarVec Lynx.Rustler.decodeBool (.cons (.atom "true") (.integer tail)) =
      .error (.error (.atom "nif_panicked")) :=
  Lynx.Rustler.decodeScalarVec_improper _ _ true _ rfl

theorem signed_head_range_error (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64)
      (.cons (.integer 9223372036854775808) tail) = .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem oversized_encoding_exhausts (value : alloc.vec.Vec I64)
    (large : Lynx.Rustler.byteVecLimit < value.val.length) :
    Lynx.Rustler.execute (Lynx.Rustler.encodeScalarVec Lynx.Rustler.encodeSigned value) id =
      .error .exhausted := by
  rw [Lynx.Rustler.encodeScalarVec_exhausted _ _ large]
  exact Lynx.Rustler.execute_undef _

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.ScalarFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.ScalarVec
end RustWorkspace.ScalarVec
