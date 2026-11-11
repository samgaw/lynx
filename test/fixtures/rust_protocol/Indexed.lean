module
public import Indexed.WindowProperties
public section
open Aeneas Aeneas.Std
namespace Indexed.Properties

theorem core_prefix (input : Slice U8) (stop : Usize) :
    __CORE__.protocol.indexed_prefix input stop =
      if stop.val ≤ input.val.length then RustM.ok (expectedWindow input 0#usize stop)
      else RustM.fail .panic := by
  by_cases h : stop.val ≤ input.val.length
  all_goals simp [__CORE__.protocol.indexed_prefix, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index, expectedWindow, h]

theorem exact_consumption (input : Slice U8) (position : Usize)
    (valid : position.val ≤ input.val.length) :
    (do let output ← __ANALYSIS__.indexed_split input position
        pure (output.1.val ++ output.2.val)) = RustM.ok input.val := by
  have remainder : (input.val.drop position.val).take (input.val.length - position.val) =
      input.val.drop position.val := by
    simpa only [List.length_drop] using (List.take_length : (input.val.drop position.val).take (input.val.drop position.val).length = _)
  simp [__ANALYSIS__.indexed_split, core_prefix, core_window, valid,
    expectedWindow, Slice.len, List.slice, pure, remainder]

theorem split_panics (input : Slice U8) (position : Usize)
    (invalid : input.val.length < position.val) :
    __ANALYSIS__.indexed_split input position = RustM.fail .panic := by
  simp [__ANALYSIS__.indexed_split, core_prefix, Nat.not_le_of_lt invalid]

theorem array_success : __ANALYSIS__.array_window_length 1#usize 3#usize = RustM.ok 2#u64 := by
  simp [__ANALYSIS__.array_window_length, __CORE__.protocol.array_window_length,
    core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index, lift]
  apply UScalar.eq_of_val_eq
  have widen (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
    apply UScalar.cast_val_mod_pow_greater_numBits_eq
    cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  simp [widen, Slice.len, List.slice]

theorem array_panics : __ANALYSIS__.array_window_length 3#usize 1#usize = RustM.fail .panic := by
  simp [__ANALYSIS__.array_window_length, __CORE__.protocol.array_window_length,
    core.array.Array.index, core.ops.index.IndexSlice, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index, lift]

end Indexed.Properties
