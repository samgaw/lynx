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

end NamedArrayNif.Properties
