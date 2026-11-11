module
public import BorrowedPrefix.Extraction.Funs
public import BorrowedPrefix.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace BorrowedPrefix.Properties

private theorem widen (length : U8) : (UScalar.cast .Usize length).val = length.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

def expectedPrefix (input : Slice U8) (length : U8) : Slice U8 :=
  .from (input.val.take length.val) (by simpa only [List.length_take] using le_trans (Nat.min_le_right _ _) input.property)

theorem core_spec (input : Slice U8) (length : U8) :
    experiment_nif.experiment_core.protocol.prefix input length = RustM.ok
      (if length.val ≤ input.val.length then some (expectedPrefix input length) else none) := by
  by_cases h : length.val ≤ input.val.length
  all_goals simp [experiment_nif.experiment_core.protocol.prefix, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeToUsizeSlice.get, lift, widen, Slice.length,
    List.slice, expectedPrefix, h]

theorem bytes_spec (input : Slice U8) (length : U8) :
    (do let output ← experiment_nif.experiment_core.protocol.prefix input length
        pure (output.map Slice.val)) =
      RustM.ok (if length.val ≤ input.val.length then some (input.val.take length.val) else none) := by
  rw [core_spec]
  split <;> simp_all [expectedPrefix, pure]

theorem caller_spec (input : Slice U8) (length : U8) :
    experiment_nif.experiment_analysis.prefix_length input length = RustM.ok
      (if length.val ≤ input.val.length then some (UScalar.cast .U64 length) else none) := by
  simp only [experiment_nif.experiment_analysis.prefix_length, core_spec]
  split
  · rename_i h
    simp [core.option.Option.map,
      experiment_nif.experiment_analysis.prefix_length.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8U64.call_once,
      expectedPrefix, Slice.len, List.length_take, Nat.min_eq_left h, lift]
    apply UScalar.eq_of_val_eq
    simp [UScalar.cast_val_eq]
  · simp [core.option.Option.map]

theorem facade_spec (value : Lynx.Rustler.Binary) (length : U8)
    (unsigned : value.size ≤ Usize.max) (signed : value.size ≤ Isize.max.toNat) :
    __FACADE__ value length = RustM.ok
      (if length.val ≤ value.size then some (UScalar.cast .U64 length) else none) := by
  obtain ⟨slice, decoded, size⟩ := Lynx.Rustler.binaryAsSlice_spec value unsigned signed
  simp [__FACADE__,
    decoded, caller_spec, size]
end BorrowedPrefix.Properties
