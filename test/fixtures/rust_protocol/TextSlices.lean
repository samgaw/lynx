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


end TextSlices.Properties
