module
public import Window.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace Window.Properties

def expectedWindow (input : Slice U8) (start stop : Usize) : Slice U8 :=
  .from (input.val.slice start.val stop.val) (by
    have := input.property
    simp only [List.slice, List.length_take, List.length_drop]
    omega)

theorem core_window (input : Slice U8) (start stop : Usize) :
    slice_analysis.slice_base.window input start stop = RustM.ok
      (if start.val ≤ stop.val ∧ stop.val ≤ input.val.length then
        some (expectedWindow input start stop) else none) := by
  by_cases h : start.val ≤ stop.val ∧ stop.val ≤ input.val.length
  all_goals simp [slice_analysis.slice_base.window, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeUsizeSlice.get, expectedWindow, h]

theorem core_remainder (input : Slice U8) (start : Usize) :
    slice_analysis.slice_base.remainder input start = RustM.ok
      (if start.val ≤ input.val.length then some (input.drop start) else none) := by
  by_cases h : start.val ≤ input.val.length
  all_goals simp [slice_analysis.slice_base.remainder, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeFromUsizeSlice.get, h]

theorem window_bytes (input : Slice U8) (start stop : Usize) :
    (do let output ← slice_analysis.window input start stop; pure (output.map Slice.val)) = RustM.ok
      (if start.val ≤ stop.val ∧ stop.val ≤ input.val.length then
        some ((input.val.drop start.val).take (stop.val - start.val)) else none) := by
  simp only [slice_analysis.window, core_window]
  split <;> simp_all [expectedWindow, List.slice, pure]

theorem remainder_bytes (input : Slice U8) (start : Usize) :
    (do let output ← slice_analysis.remainder input start; pure (output.map Slice.val)) = RustM.ok
      (if start.val ≤ input.val.length then some (input.val.drop start.val) else none) := by
  simp only [slice_analysis.remainder, core_remainder]
  split <;> simp_all [Slice.drop, pure]

theorem split_bytes (input : Slice U8) (position : Usize) :
    (do let output ← slice_analysis.split input position
        pure (output.map fun parts => (parts.1.val, parts.2.val))) = RustM.ok
      (if position.val ≤ input.val.length then
        some (input.val.take position.val, input.val.drop position.val) else none) := by
  by_cases h : position.val ≤ input.val.length
  all_goals simp [slice_analysis.split, core_window, core_remainder, h,
    expectedWindow, Slice.drop, List.slice, lift, pure]

theorem exact_consumption (input : Slice U8) (position : Usize)
    (h : position.val ≤ input.val.length) :
    (do let output ← slice_analysis.split input position
        pure (output.map fun parts => parts.1.val ++ parts.2.val)) = RustM.ok (some input.val) := by
  simp [slice_analysis.split, core_window, core_remainder, h,
    expectedWindow, Slice.drop, List.slice, lift, pure]

theorem consumption_sizes (input : Slice U8) (position : Usize)
    (h : position.val ≤ input.val.length) :
    (do let output ← slice_analysis.split input position
        pure (output.map fun parts => (parts.1.val.length, parts.2.val.length))) =
      RustM.ok (some (position.val, input.val.length - position.val)) := by
  simp [slice_analysis.split, core_window, core_remainder, h,
    expectedWindow, Slice.drop, List.slice, lift, pure, List.length_take, Nat.min_eq_left h]
end Window.Properties
