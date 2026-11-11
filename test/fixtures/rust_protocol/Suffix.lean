module
public import Consume.Properties
public section
open Aeneas Aeneas.Std
namespace Consume.Properties

@[expose] def head (input : Slice U8) (count : Nat) : Slice U8 :=
  .from (input.val.take count) (by simpa only [List.length_take] using le_trans (Nat.min_le_right count input.val.length) input.property)

theorem suffix_bytes (input needle : Slice U8) :
    __CORE__.consume_suffix core.cmp.PartialEqU8 input needle =
      RustM.ok (if needle.val.length ≤ input.val.length ∧ input.val.drop (input.val.length - needle.val.length) = needle.val
        then some (head input (input.val.length - needle.val.length)) else none) := by
  by_cases h : needle.val.length ≤ input.val.length
  · have spec := UScalar.sub_bv_spec (x := Slice.len input) (y := Slice.len needle) (by simpa [Slice.len] using h)
    cases computation : (Slice.len input - Slice.len needle) with
    | ret delta =>
      simp only [computation, WP.spec_ok] at spec
      have value : delta.val = input.val.length - needle.val.length := by simpa [Slice.len] using spec.1
      have bounded : delta.val ≤ input.val.length := by rw [value]; omega
      simp only [Slice.len] at computation
      by_cases equal : input.val.drop (input.val.length - needle.val.length) = needle.val
      all_goals simp [__CORE__.consume_suffix, __ROOT__.core.slice.Slice.strip_suffix,
        __ROOT__.Slice.Insts.CoreSliceSlicePattern.as_slice,
        core.slice.Slice.split_at, Slice.len, slice_equal, Slice.eq_iff, head, computation, value, bounded, h, equal]
    | vis effect continuation => simp only [computation, WP.spec_vis] at spec
    | div => simp only [computation, WP.spec_div] at spec
  · simp [__CORE__.consume_suffix, __ROOT__.core.slice.Slice.strip_suffix,
      __ROOT__.Slice.Insts.CoreSliceSlicePattern.as_slice, Slice.len, h]


theorem suffix_conservation (input needle remaining : Slice U8)
    (returned : __CORE__.consume_suffix core.cmp.PartialEqU8 input needle = RustM.ok (some remaining)) :
    remaining.val ++ needle.val = input.val := by
  rw [suffix_bytes] at returned
  split at returned
  · rename_i valid
    simp only [RustM.ok.injEq, Option.some.injEq] at returned
    subst remaining
    simpa [head, valid.2] using List.take_append_drop (input.val.length - needle.val.length) input.val
  · simp at returned

theorem empty_suffix (input : Slice U8) :
    __CORE__.consume_suffix core.cmp.PartialEqU8 input (.from [] (by simp)) = RustM.ok (some input) := by
  let vacant : Slice U8 := .from [] (by simp)
  change __CORE__.consume_suffix core.cmp.PartialEqU8 input vacant = _
  have value : vacant.val = [] := Slice.from_val [] _
  have unchanged : head input input.val.length = input := by
    unfold head
    simp only [List.take_length]
    exact Slice.val_from input _
  rw [suffix_bytes, value]
  simp [unchanged]

@[expose] def frame (input : Slice U8) : Option (Slice U8) :=
  if 4 ≤ input.val.length ∧ input.val.take 4 = magic then
    let rest := tail input 4
    if 2 ≤ rest.val.length ∧ rest.val.drop (rest.val.length - 2) = [13#u8,10#u8]
      then some (head rest (rest.val.length - 2)) else none
  else none

theorem frame_bytes (input : Slice U8) :
    __ANALYSIS__.consume_frame input = RustM.ok (frame input) := by
  by_cases accepted : 4 ≤ input.val.length ∧ input.val.take 4 = magic
  all_goals simp [__ANALYSIS__.consume_frame, marker_bytes, accepted, suffix_bytes, frame, lift]

theorem frame_conservation (input payload : Slice U8)
    (returned : __ANALYSIS__.consume_frame input = RustM.ok (some payload)) :
    magic ++ payload.val ++ [13#u8,10#u8] = input.val := by
  rw [frame_bytes] at returned
  simp only [RustM.ok.injEq] at returned
  unfold frame at returned
  split at returned
  · rename_i header
    dsimp only at returned
    split at returned
    · rename_i footer
      simp only [Option.some.injEq] at returned
      subst payload
      have front : magic ++ (tail input 4).val = input.val := by
        simpa [tail, header.2] using List.take_append_drop 4 input.val
      have back : (head (tail input 4) ((tail input 4).val.length - 2)).val ++ [13#u8,10#u8] = (tail input 4).val := by
        simpa [head, footer.2] using List.take_append_drop ((tail input 4).val.length - 2) (tail input 4).val
      rw [List.append_assoc, back, front]
    · simp at returned
  · simp at returned

theorem frame_length_bound (input payload : Slice U8)
    (returned : __ANALYSIS__.consume_frame input = RustM.ok (some payload)) :
    payload.val.length + 6 = input.val.length := by
  have size := congrArg List.length (frame_conservation input payload returned)
  simp [magic, List.length_append] at size
  omega

theorem frame_length_bytes (input : Slice U8) :
    __ANALYSIS__.frame_length input = RustM.ok ((frame input).map
      (fun payload => UScalar.cast .U64 (Slice.len payload))) := by
  cases h : frame input <;>
    simp [__ANALYSIS__.frame_length, frame_bytes, h, core.option.Option.map,
      __ANALYSIS__.frame_length.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8U64.call_once]

theorem suffix_panic : __ANALYSIS__.checked_suffix = RustM.fail .panic := by
  have one (h : 1 < 2^UScalarTy.Usize.numBits) : Usize.ofNatCore 1 h = 1#usize := by
    apply UScalar.eq_of_val_eq
    simp
  have subtraction : ((1#usize) - (1#usize) : RustM Usize) = RustM.ok 0#usize := by rfl
  simp [__ANALYSIS__.checked_suffix, __CORE__.checked_suffix,
    __ROOT__.core.slice.Slice.strip_suffix,
    __ROOT__.Array.Insts.CoreSliceSlicePattern.as_slice,
    __CORE__.CheckedByte.Insts.CoreCmpPartialEqCheckedByte.ne,
    core.slice.Slice.split_at, core.slice.cmp.PartialEqSlice.eq,
    Lynx.RustFormatting.core.fmt.Arguments.from_str, one, subtraction, Slice.len, lift, pure]

end Consume.Properties
