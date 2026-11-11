module
public import Indexed.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace Indexed.Properties

@[expose] def expectedWindow (input : Slice U8) (start stop : Usize) : Slice U8 :=
  .from (input.val.slice start.val stop.val) (by
    have := input.property
    simp only [List.slice, List.length_take, List.length_drop]
    omega)

theorem core_window (input : Slice U8) (start stop : Usize) :
    __CORE__.protocol.indexed_window input start stop =
      if start.val ≤ stop.val ∧ stop.val ≤ input.val.length then
        RustM.ok (expectedWindow input start stop) else RustM.fail .panic := by
  by_cases h : start.val ≤ stop.val ∧ stop.val ≤ input.val.length
  all_goals simp [__CORE__.protocol.indexed_window, core.slice.index.Slice.index,
    core.slice.index.SliceIndexRangeUsizeSlice.index, expectedWindow, h]

theorem window_bytes (input : Slice U8) (start stop : Usize) :
    (do let output ← __ANALYSIS__.indexed_window input start stop
        pure output.val) =
      if start.val ≤ stop.val ∧ stop.val ≤ input.val.length then
        RustM.ok ((input.val.drop start.val).take (stop.val - start.val))
      else RustM.fail .panic := by
  by_cases h : start.val ≤ stop.val ∧ stop.val ≤ input.val.length
  all_goals simp [__ANALYSIS__.indexed_window, core_window, h, expectedWindow, List.slice, pure]

end Indexed.Properties
