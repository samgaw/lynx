module
public import BorrowedConstants.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace BorrowedConstants.Properties

theorem marker_bytes : experiment_analysis.experiment_core.protocol.borrowed_magic_bytes =
    RustM.ok (Slice.from [76#u8,89#u8,78#u8,88#u8] (by scalar_tac)) := by
  unfold experiment_analysis.experiment_core.protocol.borrowed_magic_bytes
    experiment_analysis.experiment_core.protocol.BORROWED_MAGIC
  rfl

theorem binary_bytes : experiment_analysis.experiment_core.protocol.binary_tag_bytes =
    RustM.ok (Slice.from [76#u8,0#u8,255#u8] (by scalar_tac)) := by
  unfold experiment_analysis.experiment_core.protocol.binary_tag_bytes
    experiment_analysis.experiment_core.protocol.BINARY_TAG
  rfl

theorem core_word : experiment_analysis.experiment_core.protocol.borrowed_magic_word =
    RustM.ok (some 1280921176#u32) := by
  simp [experiment_analysis.experiment_core.protocol.borrowed_magic_word, marker_bytes,
    experiment_analysis.experiment_core.protocol.read_header, UScalar.lt_equiv,
    Slice.index_usize, lift]
  rfl

theorem caller_word : experiment_analysis.borrowed_magic_word = RustM.ok (some 1280921176#u32) := by
  simp [experiment_analysis.borrowed_magic_word, core_word]

theorem caller_binary : experiment_analysis.binary_tag_bytes =
    RustM.ok (Slice.from [76#u8,0#u8,255#u8] (by scalar_tac)) := by
  simp [experiment_analysis.binary_tag_bytes, binary_bytes]

end BorrowedConstants.Properties
