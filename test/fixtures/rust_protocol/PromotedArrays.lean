module
public import PromotedArrays.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace PromotedArrays.Properties

theorem core_empty :
    experiment_analysis.experiment_core.protocol.default_bytes =
      RustM.ok (Slice.from ([] : List U8) (by simp)) := by
  rfl

theorem core_magic :
    experiment_analysis.experiment_core.protocol.magic_bytes =
      RustM.ok (Slice.from [76#u8, 89#u8, 78#u8, 88#u8] (by scalar_tac)) := by
  rfl

theorem empty :
    experiment_analysis.default_bytes = RustM.ok (Slice.from ([] : List U8) (by simp)) := by
  simp [experiment_analysis.default_bytes, core_empty]

theorem magic :
    experiment_analysis.magic_bytes =
      RustM.ok (Slice.from [76#u8, 89#u8, 78#u8, 88#u8] (by scalar_tac)) := by
  simp [experiment_analysis.magic_bytes, core_magic]

end PromotedArrays.Properties
