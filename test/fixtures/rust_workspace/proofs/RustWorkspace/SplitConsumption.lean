module
public import BorrowedPrefix.Extraction.Funs
public import BorrowedPrefix.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace BorrowedPrefix.Consumption

private theorem widen8 (value : U8) : (UScalar.cast .Usize value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem widen64 (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

def expectedWindow (input : Slice U8) (start stop : Usize) : Slice U8 :=
  .from (input.val.slice start.val stop.val) (by
    have := input.property
    simp only [List.slice, List.length_take, List.length_drop]
    omega)

theorem window_spec (input : Slice U8) (start stop : Usize) :
    experiment_nif.experiment_core.protocol.window input start stop = RustM.ok
      (if start.val ≤ stop.val ∧ stop.val ≤ input.val.length then
        some (expectedWindow input start stop) else none) := by
  by_cases h : start.val ≤ stop.val ∧ stop.val ≤ input.val.length
  all_goals simp [experiment_nif.experiment_core.protocol.window, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeUsizeSlice.get, expectedWindow, h]

theorem remainder_spec (input : Slice U8) (start : Usize) :
    experiment_nif.experiment_core.protocol.remainder input start = RustM.ok
      (if start.val ≤ input.val.length then some (input.drop start) else none) := by
  by_cases h : start.val ≤ input.val.length
  all_goals simp [experiment_nif.experiment_core.protocol.remainder, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeFromUsizeSlice.get, h]

theorem parser_spec (input : Slice U8) (position : Usize) :
    experiment_nif.experiment_analysis.split_payload input position = RustM.ok
      (if position.val ≤ input.val.length then
        some (expectedWindow input 0#usize position, input.drop position) else none) := by
  by_cases h : position.val ≤ input.val.length
  all_goals simp [experiment_nif.experiment_analysis.split_payload, window_spec, remainder_spec,
    h, lift]

theorem exact_bytes (input : Slice U8) (position : Usize) :
    (do let output ← experiment_nif.experiment_analysis.split_payload input position
        pure (output.map fun parts => (parts.1.val, parts.2.val))) = RustM.ok
      (if position.val ≤ input.val.length then
        some (input.val.take position.val, input.val.drop position.val) else none) := by
  rw [parser_spec]
  split <;> simp_all [expectedWindow, Slice.drop, List.slice, pure]

theorem reconstruct (input : Slice U8) (position : Usize) (h : position.val ≤ input.val.length) :
    (do let output ← experiment_nif.experiment_analysis.split_payload input position
        pure (output.map fun parts => parts.1.val ++ parts.2.val)) = RustM.ok (some input.val) := by
  simp [parser_spec, h, expectedWindow, Slice.drop, List.slice, pure]

def expectedLengths (input : Slice U8) (length : U8) : Option (U64 × U64) :=
  if length.val ≤ input.val.length then
    some (UScalar.cast .U64 length, UScalar.cast .U64 (input.drop (UScalar.cast .Usize length)).len)
  else none

theorem caller_spec (input : Slice U8) (length : U8) :
    experiment_nif.experiment_analysis.split_lengths input length = RustM.ok (expectedLengths input length) := by
  by_cases h : length.val ≤ input.val.length
  all_goals simp [experiment_nif.experiment_analysis.split_lengths, parser_spec, expectedLengths,
    core.option.Option.map,
    experiment_nif.experiment_analysis.split_lengths.closure.Insts.CoreOpsFunctionFnOnceTuplePairShared0SliceU8Shared1SliceU8PairU64U64.call_once,
    expectedWindow, Slice.len, List.slice, List.length_take, h, widen8, Nat.min_def, lift]
  apply UScalar.eq_of_val_eq
  simp [UScalar.cast_val_eq]

theorem values_spec (input : Slice U8) (length : U8) :
    (expectedLengths input length).map (fun parts => (parts.1.val, parts.2.val)) =
      if length.val ≤ input.val.length then some (length.val, input.val.length - length.val) else none := by
  by_cases h : length.val ≤ input.val.length
  all_goals simp [expectedLengths, h, widen64, widen8, Slice.len, Slice.drop]
theorem facade_spec (value : Lynx.Rustler.Binary) (length : U8)
    (unsigned : value.size ≤ Usize.max) (signed : value.size ≤ Isize.max.toNat) :
    ∃ output,
      __FACADE__ value length = RustM.ok output ∧
      output.map (fun parts => (parts.1.val, parts.2.val)) =
        if length.val ≤ value.size then some (length.val, value.size - length.val) else none := by
  obtain ⟨slice, decoded, size⟩ := Lynx.Rustler.binaryAsSlice_spec value unsigned signed
  refine ⟨expectedLengths slice length, ?_, ?_⟩
  · simp [__FACADE__, decoded, caller_spec]
  · simpa only [size] using values_spec slice length

end BorrowedPrefix.Consumption
