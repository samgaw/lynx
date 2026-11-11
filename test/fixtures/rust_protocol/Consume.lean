module
public import Consume.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace Consume.Properties
theorem slice_equal (left right : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right =
      RustM.ok (decide (left = right)) := by
  have spec := core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 left right
    (by intro x y; simp [core.cmp.PartialEqU8])
  cases computation : core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right with
  | ret value =>
    simp only [computation, WP.spec_ok] at spec
    have equality : value = decide (left = right) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq] using spec
    exact congrArg RustM.ok equality
  | vis effect continuation => simp only [computation, WP.spec_vis] at spec
  | div => simp only [computation, WP.spec_div] at spec


@[expose] def tail (input : Slice U8) (count : Nat) : Slice U8 :=
  .from (input.val.drop count) (by have := input.property; simp only [List.length_drop]; omega)

theorem consume_bytes (input needle : Slice U8) :
    __CORE__.consume_prefix core.cmp.PartialEqU8 input needle =
      RustM.ok (if needle.val.length ≤ input.val.length ∧ input.val.take needle.val.length = needle.val
        then some (tail input needle.val.length) else none) := by
  by_cases h : needle.val.length ≤ input.val.length
  all_goals by_cases equal : input.val.take needle.val.length = needle.val
  all_goals simp [__CORE__.consume_prefix, __ROOT__.core.slice.Slice.strip_prefix,
    __ROOT__.Slice.Insts.CoreSliceSlicePattern,
    __ROOT__.Slice.Insts.CoreSliceSlicePattern.as_slice,
    core.slice.Slice.split_at, Slice.len, slice_equal, Slice.eq_iff, tail, h, equal]

theorem conservation (input needle remaining : Slice U8)
    (returned : __CORE__.consume_prefix core.cmp.PartialEqU8 input needle = RustM.ok (some remaining)) :
    needle.val ++ remaining.val = input.val := by
  rw [consume_bytes] at returned
  split at returned
  · rename_i valid
    simp only [RustM.ok.injEq, Option.some.injEq] at returned
    subst remaining
    simpa [tail, valid.2] using List.take_append_drop needle.val.length input.val
  · simp at returned

@[expose] def magic : List U8 := [76#u8,89#u8,78#u8,88#u8]

theorem marker_bytes (input : Slice U8) :
    __ANALYSIS__.consume_marker input = RustM.ok
      (if 4 ≤ input.val.length ∧ input.val.take 4 = magic then some (tail input 4) else none) := by
  unfold __ANALYSIS__.consume_marker
  rw [consume_bytes]
  simp [__CORE__.BORROWED_MAGIC, magic]
  split <;> simp_all
  rename_i invalid
  symm
  apply if_neg
  rintro ⟨size, bytes⟩
  exact invalid size bytes

theorem length_bytes (input : Slice U8) :
    __ANALYSIS__.consumed_length input = RustM.ok
      (if 4 ≤ input.val.length ∧ input.val.take 4 = magic
        then some (UScalar.cast .U64 (Slice.len (tail input 4))) else none) := by
  by_cases size : 4 ≤ input.val.length
  all_goals by_cases bytes : input.val.take 4 = magic
  all_goals simp [__ANALYSIS__.consumed_length, marker_bytes, size, bytes, lift,
    core.option.Option.map,
    __ANALYSIS__.consumed_length.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8U64.call_once]

theorem empty_prefix (input : Slice U8) :
    __CORE__.consume_prefix core.cmp.PartialEqU8 input (.from [] (by simp)) = RustM.ok (some input) := by
  let vacant : Slice U8 := .from [] (by simp)
  change __CORE__.consume_prefix core.cmp.PartialEqU8 input vacant = _
  have value : vacant.val = [] := Slice.from_val [] _
  have unchanged : tail input 0 = input := by
    unfold tail
    simp only [List.drop_zero]
    exact Slice.val_from input _
  rw [consume_bytes, value]
  simp [unchanged]

theorem comparator_panic : __ANALYSIS__.checked_consume = RustM.fail .panic := by
  simp [__ANALYSIS__.checked_consume, __CORE__.checked_consume,
    __ROOT__.core.slice.Slice.strip_prefix,
    __ROOT__.Array.Insts.CoreSliceSlicePattern.as_slice,
    __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte.ne,
    core.slice.Slice.split_at, core.slice.cmp.PartialEqSlice.eq,
    Lynx.RustFormatting.core.fmt.Arguments.from_str, lift, pure]

theorem recognize_without_panic : __ANALYSIS__.checked_recognize = RustM.ok false := by
  simp [__ANALYSIS__.checked_recognize, __CORE__.checked_recognize,
    __ROOT__.core.slice.Slice.starts_with,
    __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte.ne,
    core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.cmp.PartialEqSlice.eq, lift, pure]

end Consume.Properties
