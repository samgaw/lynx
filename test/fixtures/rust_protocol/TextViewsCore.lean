module
public import TextCore.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace TextCore.Properties

theorem bytes_spec (text : Str) :
    experiment_core.protocol.text_bytes text = RustM.ok (α := Slice U8) text := by
  rfl

theorem length_spec (text : Str) :
    (do let count ← experiment_core.protocol.text_length text
        pure count.val) = RustM.ok text.val.length := by
  simp [experiment_core.protocol.text_length, pure]

theorem empty_spec (text : Str) :
    experiment_core.protocol.text_empty text = RustM.ok (decide (text.val.length = 0)) := by
  simp [experiment_core.protocol.text_empty, core.slice.Slice.is_empty]

theorem boundary_spec (text : Str) (position : Usize) :
    experiment_core.protocol.text_boundary text position = .ok
      (if position.val = 0 then true
       else match text.val[position.val]? with
       | some byte => decide (byte.val < 128 ∨ 192 ≤ byte.val)
       | none => decide (position.val = text.val.length)) := by
  rfl

theorem boundary_zero (text : Str) :
    experiment_core.protocol.text_boundary text 0#usize = .ok true := by
  simp [boundary_spec]

theorem boundary_end (text : Str) :
    experiment_core.protocol.text_boundary text (Slice.len text) = .ok true := by
  simp [boundary_spec, Slice.len]

theorem boundary_past_end (text : Str) (position : Usize)
    (past : text.val.length < position.val) :
    experiment_core.protocol.text_boundary text position = .ok false := by
  have nonzero : position.val ≠ 0 := by omega
  have absent : text.val[position.val]? = none := List.getElem?_eq_none (by omega)
  simp [boundary_spec, nonzero, absent, Nat.ne_of_gt past]

theorem boundary_unicode :
    let text := Slice.from [97#u8, 195#u8, 169#u8, 240#u8, 159#u8, 153#u8, 130#u8, 122#u8]
      (by scalar_tac)
    [0#usize, 1#usize, 2#usize, 3#usize, 4#usize, 5#usize, 6#usize, 7#usize, 8#usize, 9#usize].map
      (experiment_core.protocol.text_boundary text) =
    [.ok true, .ok true, .ok false, .ok true, .ok false, .ok false, .ok false,
     .ok true, .ok true, .ok false] := by
  cbv

end TextCore.Properties
