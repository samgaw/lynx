module
public import TextSlices.Extraction.Funs
public section
open Aeneas Aeneas.Std
unseal RustM
namespace TextSlices.Properties

theorem window_composition (text : Str) (start stop : Usize) :
    experiment_analysis.text_window text start stop =
      experiment_analysis.experiment_core.protocol.text_window text start stop := by
  simp [experiment_analysis.text_window]


theorem window_valid (text : Str) (start stop : Usize)
    (startBoundary : TextSlices.Extraction.StringViews.isCharBoundary text start = true)
    (stopBoundary : TextSlices.Extraction.StringViews.isCharBoundary text stop = true)
    (ordered : start.val ≤ stop.val) (bounded : stop.val ≤ text.val.length) :
    (do let result ← experiment_analysis.text_window text start stop
        pure (result.map (fun (field : Str) => field.val))) =
    .ok (some (text.val.slice start.val stop.val)) := by
  simp [Str, experiment_analysis.text_window, experiment_analysis.experiment_core.protocol.text_window,
    TextSlices.Extraction.StringSlices.get, TextSlices.Extraction.StringSlices.RangeIndex,
    TextSlices.Extraction.StringSlices.rangeGet, startBoundary, stopBoundary,
    core.slice.index.SliceIndexRangeUsizeSlice.get, Slice.length, ordered, bounded, pure]

theorem split_roundtrip (text : Str) (position : Usize)
    (boundary : TextSlices.Extraction.StringViews.isCharBoundary text position = true)
    (bounded : position.val ≤ text.val.length) :
    (do let result ← experiment_analysis.split_text text position
        pure (result.map (fun (fields : Str × Str) => fields.1.val ++ fields.2.val))) = .ok (some text.val) := by
  have zero : TextSlices.Extraction.StringViews.isCharBoundary text 0#usize = true := by
    simp [TextSlices.Extraction.StringViews.isCharBoundary]
  have ending : TextSlices.Extraction.StringViews.isCharBoundary text (Slice.len text) = true := by
    simp [TextSlices.Extraction.StringViews.isCharBoundary, Slice.len]
  simp [experiment_analysis.split_text, experiment_analysis.experiment_core.protocol.text_prefix,
    experiment_analysis.experiment_core.protocol.text_suffix,
    TextSlices.Extraction.StringSlices.get, TextSlices.Extraction.StringSlices.RangeToIndex,
    TextSlices.Extraction.StringSlices.RangeFromIndex, TextSlices.Extraction.StringSlices.toGet,
    TextSlices.Extraction.StringSlices.fromGet, TextSlices.Extraction.StringSlices.rangeGet,
    Str, boundary, zero, ending, core.slice.index.SliceIndexRangeUsizeSlice.get, bounded,
    Slice.length, Slice.len, Lynx.Rust.Try.optionBranch, bind_ok, lift, pure, List.slice]
  simpa only [← List.length_drop, List.take_length] using List.take_append_drop position.val text.val

theorem split_rejected (text : Str) (position : Usize)
    (inside : TextSlices.Extraction.StringViews.isCharBoundary text position = false) :
    experiment_analysis.split_text text position = .ok none := by
  simp [experiment_analysis.split_text, experiment_analysis.experiment_core.protocol.text_prefix,
    TextSlices.Extraction.StringSlices.get, TextSlices.Extraction.StringSlices.RangeToIndex,
    TextSlices.Extraction.StringSlices.toGet, TextSlices.Extraction.StringSlices.rangeGet,
    inside, Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]

theorem windows_unicode :
    [(1#usize, 3#usize), (3#usize, 7#usize), (2#usize, 2#usize), (1#usize, 1#usize),
      (8#usize, 8#usize), (9#usize, 9#usize), (7#usize, 3#usize)].map
      (fun (bounds : Usize × Usize) =>
        experiment_analysis.text_window (toStr "aé🙂z") bounds.1 bounds.2) =
    [.ok (some (toStr "é")), .ok (some (toStr "🙂")), .ok none,
     .ok (some (toStr "")), .ok (some (toStr "")), .ok none, .ok none] := by
  cbv

theorem window_utf8 (text field : Str) (start stop : Usize)
    (valid : (Extraction.StringSlices.bytes text).IsValidUTF8)
    (returned : experiment_analysis.text_window text start stop = .ok (some field)) :
    (Extraction.StringSlices.bytes field).IsValidUTF8 := by
  apply Extraction.StringSlices.rangeGet_valid_utf8 ⟨start, stop⟩ text field valid
  exact returned

theorem split_utf8 (text left right : Str) (position : Usize)
    (valid : (Extraction.StringSlices.bytes text).IsValidUTF8)
    (returned : experiment_analysis.split_text text position = .ok (some (left, right))) :
    (Extraction.StringSlices.bytes left).IsValidUTF8 ∧
      (Extraction.StringSlices.bytes right).IsValidUTF8 := by
  obtain ⟨leftResult, hp⟩ := Extraction.StringSlices.rangeGet_returns ⟨0#usize, position⟩ text
  obtain ⟨rightResult, hs⟩ := Extraction.StringSlices.rangeGet_returns ⟨position, Slice.len text⟩ text
  have pre : experiment_analysis.experiment_core.protocol.text_prefix text position = .ok leftResult := hp
  have suf : experiment_analysis.experiment_core.protocol.text_suffix text position = .ok rightResult := hs
  simp only [experiment_analysis.split_text, pre, suf, bind_ok, Lynx.Rust.Try.optionBranch, lift] at returned
  cases leftResult with
  | none => simp [Lynx.Rust.Try.optionFromResidual] at returned
  | some first =>
    cases rightResult with
    | none => simp [Lynx.Rust.Try.optionFromResidual] at returned
    | some second =>
      simp only [RustM.ok.injEq, Option.some.injEq, Prod.mk.injEq] at returned
      rcases returned with ⟨rfl, rfl⟩
      exact ⟨Extraction.StringSlices.rangeGet_valid_utf8 _ _ _ valid hp,
        Extraction.StringSlices.rangeGet_valid_utf8 _ _ _ valid hs⟩


theorem checked_implementation (text : Str) (position : Usize) :
    experiment_analysis.checked_text_split text position =
      (if TextSlices.Extraction.StringViews.isCharBoundary text position then do
        let fields ← TextSlices.Extraction.StringSlices.splitUnchecked text position
        pure (some fields)
       else .ok none) := by
  rfl

theorem checked_consistent (text : Str) (position : Usize)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8) :
    experiment_analysis.checked_text_split text position = experiment_analysis.split_text text position := by
  rw [checked_implementation]
  cases boundary : TextSlices.Extraction.StringViews.isCharBoundary text position with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact (split_rejected text position boundary).symm
  | true =>
    have bounded : position.val ≤ text.val.length := by
      have pos := TextSlices.Extraction.StringSlices.boundary_valid text valid position boundary
      have bound := pos.le_rawEndPos
      simpa [String.Pos.Raw.le_iff, String.rawEndPos, String.utf8ByteSize] using bound
    have zero : TextSlices.Extraction.StringViews.isCharBoundary text 0#usize = true := by
      simp [TextSlices.Extraction.StringViews.isCharBoundary]
    have ending : TextSlices.Extraction.StringViews.isCharBoundary text (Slice.len text) = true := by
      simp [TextSlices.Extraction.StringViews.isCharBoundary, Slice.len]
    simp [Str, TextSlices.Extraction.StringSlices.splitUnchecked, boundary,
      core.slice.Slice.split_at, bounded, UScalar.le_equiv, Slice.length,
      experiment_analysis.split_text, experiment_analysis.experiment_core.protocol.text_prefix,
      experiment_analysis.experiment_core.protocol.text_suffix, TextSlices.Extraction.StringSlices.get,
      TextSlices.Extraction.StringSlices.RangeToIndex, TextSlices.Extraction.StringSlices.RangeFromIndex,
      TextSlices.Extraction.StringSlices.toGet, TextSlices.Extraction.StringSlices.fromGet,
      TextSlices.Extraction.StringSlices.rangeGet, zero, ending, Slice.len,
      core.slice.index.SliceIndexRangeUsizeSlice.get, Lynx.Rust.Try.optionBranch,
      lift, pure, List.slice, List.splitAt_eq]
    simp only [← List.length_drop, List.take_length]

theorem checked_rejected (text : Str) (position : Usize)
    (rejected : TextSlices.Extraction.StringViews.isCharBoundary text position = false) :
    experiment_analysis.checked_text_split text position = .ok none := by
  simp [checked_implementation, rejected]

theorem checked_utf8 (text left right : Str) (position : Usize)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (returned : experiment_analysis.checked_text_split text position = .ok (some (left, right))) :
    (TextSlices.Extraction.StringSlices.bytes left).IsValidUTF8 ∧
      (TextSlices.Extraction.StringSlices.bytes right).IsValidUTF8 := by
  exact split_utf8 text left right position valid (by rwa [← checked_consistent text position valid])

@[cbv_eval] theorem checked_by_values (text : Str) (position : Usize) :
    experiment_analysis.checked_text_split text position =
      if TextSlices.Extraction.StringViews.isCharBoundary text position then
        .ok (some (Slice.from (text.val.take position.val) (by scalar_tac), text.drop position))
      else .ok none := by
  rw [checked_implementation]
  cases boundary : TextSlices.Extraction.StringViews.isCharBoundary text position with
  | false => rfl
  | true =>
    have bounded : position.val ≤ text.val.length := by
      by_cases zero : position.val = 0
      · omega
      · by_cases inside : position.val < text.val.length
        · omega
        · have absent : text.val[position.val]? = none := List.getElem?_eq_none (by omega)
          have ending : position.val = text.val.length := by
            simpa [TextSlices.Extraction.StringViews.isCharBoundary, zero, absent] using boundary
          omega
    simp [Str, TextSlices.Extraction.StringSlices.splitUnchecked, boundary,
      core.slice.Slice.split_at, bounded, Slice.length,
      Slice.drop, List.splitAt_eq, pure]

private theorem slice_equal (left right : Slice U8) :
    core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right =
      RustM.ok (decide (left.val = right.val)) := by
  have spec := core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 left right
    (by intro x y; simp [core.cmp.PartialEqU8])
  cases computation : core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right with
  | ret value =>
    simp only [computation, WP.spec_ok] at spec
    have equality : value = decide (left.val = right.val) := by
      apply Bool.eq_iff_iff.mpr
      simpa only [decide_eq_true_eq, Slice.eq_iff] using spec
    exact congrArg RustM.ok equality
  | vis effect continuation => simp only [computation, WP.spec_vis] at spec
  | div => simp only [computation, WP.spec_div] at spec


@[cbv_eval] theorem text_equal_bytes (left right : Str) :
    experiment_analysis.text_equal left right = .ok (decide (left.val = right.val)) := by
  change core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 left right = _
  exact slice_equal left right

theorem text_equal_reflexive (text : Str) :
    experiment_analysis.text_equal text text = .ok true := by
  simp [text_equal_bytes]

@[cbv_eval] theorem text_prefix_bytes (text needle : Str) :
    experiment_analysis.text_has_prefix text needle =
      if needle.val.length ≤ text.val.length then
        .ok (decide (needle.val = text.val.take needle.val.length))
      else .ok false := by
  change experiment_analysis.core.slice.Slice.starts_with core.cmp.PartialEqU8 text needle = _
  unfold Str at text needle
  by_cases bounded : needle.val.length ≤ text.val.length
  all_goals simp [experiment_analysis.core.slice.Slice.starts_with,
    core.slice.index.Slice.index, core.slice.index.SliceIndexRangeToUsizeSlice.index,
    Slice.len, slice_equal, List.slice, bounded]

theorem text_prefix_reflexive (text : Str) :
    experiment_analysis.text_has_prefix text text = .ok true := by
  simp [text_prefix_bytes]

theorem consume_implementation (text needle : Str) :
    experiment_analysis.text_consume_prefix text needle =
      (do let accepted ← experiment_analysis.text_has_prefix text needle
          if accepted then
            let field ← TextSlices.Extraction.StringSlices.uncheckedFrom text ⟨Slice.len needle⟩
            pure (some field)
          else .ok none) := by
  rfl

@[cbv_eval] theorem consume_by_values (text needle : Str) :
    experiment_analysis.text_consume_prefix text needle =
      if needle.val.length ≤ text.val.length ∧ needle.val = text.val.take needle.val.length then
        if TextSlices.Extraction.StringViews.isCharBoundary text (Slice.len needle) then
          .ok (some (text.drop (Slice.len needle)))
        else .fail .undef
      else .ok none := by
  by_cases bounded : needle.val.length ≤ text.val.length
  · by_cases matched : needle.val = text.val.take needle.val.length
    · have ending : TextSlices.Extraction.StringViews.isCharBoundary text (Slice.len text) = true := by
        simp [TextSlices.Extraction.StringViews.isCharBoundary, Slice.len]
      rw [if_pos ⟨bounded, matched⟩, consume_implementation, text_prefix_bytes, if_pos bounded]
      have accepted : decide (needle.val = text.val.take needle.val.length) = true := by simpa only [decide_eq_true_eq] using matched
      simp only [accepted, bind_ok, ↓reduceIte]
      cases boundary : TextSlices.Extraction.StringViews.isCharBoundary text (Slice.len needle) with
      | false =>
        simp [TextSlices.Extraction.StringSlices.uncheckedFrom, TextSlices.Extraction.StringSlices.fromGet,
          TextSlices.Extraction.StringSlices.rangeGet, boundary]
        rw [map_eq_pure_bind]
        exact bind_tc_fail _ _
      | true =>
        simp [Str, bounded,
          TextSlices.Extraction.StringSlices.uncheckedFrom, TextSlices.Extraction.StringSlices.fromGet,
          TextSlices.Extraction.StringSlices.rangeGet, boundary, ending,
          core.slice.index.SliceIndexRangeUsizeSlice.get, Slice.len, List.slice, Slice.drop]
        simp only [← List.length_drop, List.take_length]
        exact map_pure _ _
    · simp [consume_implementation, text_prefix_bytes, bounded, matched]
  · simp [consume_implementation, text_prefix_bytes, bounded]

theorem consume_exact (text needle : Str)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (needleValid : (TextSlices.Extraction.StringSlices.bytes needle).IsValidUTF8) :
    experiment_analysis.text_consume_prefix text needle =
      if needle.val.length ≤ text.val.length ∧ needle.val = text.val.take needle.val.length then
        .ok (some (text.drop (Slice.len needle)))
      else .ok none := by
  rw [consume_by_values]
  split
  · rename_i matched
    simp only [TextSlices.Extraction.StringSlices.prefix_boundary text needle valid needleValid matched.2 matched.1,
      ↓reduceIte]
  · rfl


theorem consume_utf8 (text needle field : Str)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (returned : experiment_analysis.text_consume_prefix text needle = .ok (some field)) :
    (TextSlices.Extraction.StringSlices.bytes field).IsValidUTF8 := by
  obtain ⟨accepted, recognized⟩ : ∃ accepted, experiment_analysis.text_has_prefix text needle = .ok accepted := by
    rw [text_prefix_bytes]
    split <;> exact ⟨_, rfl⟩
  cases accepted with
  | false => simp [consume_implementation, recognized] at returned
  | true =>
    obtain ⟨result, computation⟩ := TextSlices.Extraction.StringSlices.rangeGet_returns
      ⟨Slice.len needle, Slice.len text⟩ text
    have borrowed : TextSlices.Extraction.StringSlices.fromGet ⟨Slice.len needle⟩ text = .ok result := computation
    cases result with
    | none =>
      have mapped : (some <$> (RustM.fail .undef : RustM Str)) = RustM.fail .undef := by
        rw [map_eq_pure_bind]
        exact bind_tc_fail _ _
      simp [consume_implementation, recognized, TextSlices.Extraction.StringSlices.uncheckedFrom, borrowed, mapped] at returned
    | some suffix =>
      have mapped : (some <$> RustM.ok suffix) = RustM.ok (some suffix) := map_pure _ _
      have equal : suffix = field := by
        simpa [consume_implementation, recognized, TextSlices.Extraction.StringSlices.uncheckedFrom, borrowed, mapped] using returned
      subst field
      exact TextSlices.Extraction.StringSlices.rangeGet_valid_utf8 _ _ _ valid computation

attribute [local cbv_opaque] RustM.ok RustM.fail

theorem checked_unicode :
    experiment_analysis.checked_text_split (toStr "aé🙂z") 3#usize =
      .ok (some (toStr "aé", toStr "🙂z")) ∧
    experiment_analysis.checked_text_split (toStr "aé🙂z") 2#usize = .ok none ∧
    experiment_analysis.checked_text_split (toStr "aé🙂z") 9#usize = .ok none := by
  cbv
  all_goals simp

end TextSlices.Properties
