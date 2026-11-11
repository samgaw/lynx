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

end TextCore.Properties
