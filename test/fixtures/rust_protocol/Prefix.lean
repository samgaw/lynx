module
public import Prefix.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace Prefix.Properties

@[expose] def marker : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8] (by scalar_tac)
@[expose] def payload : Slice U8 := .from [76#u8,89#u8,78#u8,88#u8,0#u8,255#u8,128#u8] (by scalar_tac)
@[expose] def empty : Slice U8 := .from [] (by simp)

private theorem slice_equal (left right : Slice U8) :
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

theorem prefix_bytes (input needle : Slice U8) :
    __CORE__.has_prefix core.cmp.PartialEqU8 input needle =
      if needle.val.length ≤ input.val.length then
        RustM.ok (decide (needle.val = input.val.take needle.val.length))
      else RustM.ok false := by
  by_cases h : needle.val.length ≤ input.val.length
  all_goals simp [__CORE__.has_prefix, __HELPER__, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index, Slice.len, slice_equal,
    Slice.eq_iff, List.slice, h]

theorem marker_exact : __ANALYSIS__.recognize marker = RustM.ok true := by
  simp [__ANALYSIS__.recognize, __CORE__.BORROWED_MAGIC, __CORE__.has_prefix,
    __HELPER__, marker, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.cmp.PartialEqSlice.eq, core.cmp.PartialEqU8, pure]

theorem marker_payload : __ANALYSIS__.recognize payload = RustM.ok true := by
  simp [__ANALYSIS__.recognize, __CORE__.BORROWED_MAGIC, __CORE__.has_prefix,
    __HELPER__, payload, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.cmp.PartialEqSlice.eq, core.cmp.PartialEqU8, pure]

theorem reject_short : __ANALYSIS__.recognize empty = RustM.ok false := by
  simp [__ANALYSIS__.recognize, __CORE__.BORROWED_MAGIC, __CORE__.has_prefix,
    __HELPER__, empty]

theorem empty_prefix (input : Slice U8) :
    __CORE__.has_prefix core.cmp.PartialEqU8 input empty = RustM.ok true := by
  simp [__CORE__.has_prefix, __HELPER__, empty, Slice.len,
    core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.cmp.PartialEqSlice.eq, pure]

theorem composition (input : Slice U8) :
    __ANALYSIS__.recognize input =
      if 4 ≤ input.val.length then
        RustM.ok (decide ([76#u8,89#u8,78#u8,88#u8] = input.val.take 4))
      else RustM.ok false := by
  simpa [__ANALYSIS__.recognize, __CORE__.BORROWED_MAGIC] using
    prefix_bytes input __CORE__.BORROWED_MAGIC

theorem short_circuit : __ANALYSIS__.checked_prefix false = RustM.ok false := by
  simp [__ANALYSIS__.checked_prefix, __CORE__.checked_prefix, __CORE__.has_prefix,
    __HELPER__, __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte,
    __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte.ne,
    core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.cmp.PartialEqSlice.eq, lift, pure]

theorem comparator_panic : __ANALYSIS__.checked_prefix true = RustM.fail .panic := by
  simp [__ANALYSIS__.checked_prefix, __CORE__.checked_prefix, __CORE__.has_prefix,
    __HELPER__, __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte,
    __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte.ne,
    core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    core.slice.cmp.PartialEqSlice.eq, Lynx.RustFormatting.core.fmt.Arguments.from_str, lift, pure]

end Prefix.Properties
