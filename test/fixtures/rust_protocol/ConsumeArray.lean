module
public import Consume.Properties
public section
open Aeneas Aeneas.Std
namespace Consume.Properties

theorem array_bytes (input : Slice U8) :
    __ANALYSIS__.consume_array_marker input = RustM.ok
      (if 4 ≤ input.val.length ∧ input.val.take 4 = magic then some (tail input 4) else none) := by
  by_cases size : 4 ≤ input.val.length
  all_goals by_cases bytes : input.val.take 4 = magic
  all_goals simp only [magic] at bytes
  all_goals simp [__ANALYSIS__.consume_array_marker, __CORE__.consume_array_marker,
    __ROOT__.core.slice.Slice.strip_prefix,
    __ROOT__.Array.Insts.CoreSliceSlicePattern.as_slice,
    core.slice.Slice.split_at, Slice.len, slice_equal, Slice.eq_iff, tail, magic, size, bytes]


end Consume.Properties
