module
public import NamedArrayNif.Extraction.Funs
public import NamedArrayNif.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace NamedArrayNif.Properties

theorem core_spec :
    experiment_nif.experiment_core.protocol.named_magic_word = RustM.ok 1280921176#u32 := by
  unfold experiment_nif.experiment_core.protocol.named_magic_word
    experiment_nif.experiment_core.protocol.WIRE_MAGIC
  rfl

theorem composition : experiment_nif.experiment_analysis.named_magic_word = RustM.ok 1280921176#u32 := by
  simp [experiment_nif.experiment_analysis.named_magic_word, core_spec]

theorem facade : __FACADE__ = RustM.ok 1280921176#u32 := by
  simp [__FACADE__, composition]

theorem borrowed_bytes :
    experiment_nif.experiment_core.protocol.borrowed_magic_bytes =
      RustM.ok (Slice.from [76#u8,89#u8,78#u8,88#u8] (by scalar_tac)) := by
  unfold experiment_nif.experiment_core.protocol.borrowed_magic_bytes
    experiment_nif.experiment_core.protocol.BORROWED_MAGIC
  rfl

theorem core_borrowed : experiment_nif.experiment_core.protocol.borrowed_magic_word =
    RustM.ok (some 1280921176#u32) := by
  simp [experiment_nif.experiment_core.protocol.borrowed_magic_word, borrowed_bytes,
    experiment_nif.experiment_core.protocol.read_header, UScalar.lt_equiv,
    Slice.index_usize, lift]
  rfl

theorem borrowed_composition : experiment_nif.experiment_analysis.borrowed_magic_word =
    RustM.ok (some 1280921176#u32) := by
  simp [experiment_nif.experiment_analysis.borrowed_magic_word, core_borrowed]

theorem borrowed_facade : __BORROWED_FACADE__ = RustM.ok (some 1280921176#u32) := by
  simp [__BORROWED_FACADE__, borrowed_composition]

end NamedArrayNif.Properties
