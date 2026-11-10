module
public import Captured.Extraction.Funs
public section
open Aeneas Aeneas.Std ownership_app
namespace Captured.Properties

theorem checked_flip (value accepted : Bool) :
    ownership_base.checked_flip value accepted = RustM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()), !value) := by
  cases accepted <;>
    simp [ownership_base.checked_flip,
      ownership_base.Flip.Insts.LynxCompilerOwnershipDestruct.drop_glue,
      ownership_base.Flip.Insts.LynxCompilerOwnershipDrop.drop]

theorem compose (first second accepted : Bool) :
    ownership_app.compose first second accepted = RustM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()),
       (if accepted then first else !first), !second) := by
  cases accepted <;>
    simp [ownership_app.compose, checked_flip,
      ownership_base.Flip.Insts.LynxCompilerOwnershipDestruct.drop_glue,
      ownership_base.Flip.Insts.LynxCompilerOwnershipDrop.drop]

end Captured.Properties
