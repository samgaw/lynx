module
public import Borrowed.Extraction.Funs
public section
open Aeneas Aeneas.Std ownership_app
namespace Borrowed.Properties

theorem flip_contract (value : Bool) : ownership_base.flip value = RustM.ok (!value) := by
  simp [ownership_base.flip, ownership_base.Flip.Insts.LynxCompilerOwnershipDestruct.drop_glue,
    ownership_base.Flip.Insts.LynxCompilerOwnershipDrop.drop]

theorem scoped_flip (value : Bool) : ownership_app.scoped_flip value = RustM.ok (!value) := by
  simp [ownership_app.scoped_flip, flip_contract]
end Borrowed.Properties
