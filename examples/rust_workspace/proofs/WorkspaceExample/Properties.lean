module
public import WorkspaceExample.Extraction.Funs
public import Lynx.Rustler
public section

open Aeneas Aeneas.Std
namespace WorkspaceExample.Properties

-- The statements name actual extracted implementations, including the internal
-- function that is not exposed through Rustler.
theorem invert_spec (value : Bool) :
    example_nif.example_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem analysis_spec (value : Bool) :
    example_nif.example_analysis.restore value = RustM.ok value := by
  simp only [example_nif.example_analysis.restore, invert_spec, bind_ok]
  cases value <;> rfl

theorem facade_spec (value : Bool) :
    example_nif.«_».__INVENTORY.nif_func.wrapper.closure.native_restore value =
      RustM.ok value := analysis_spec value

end WorkspaceExample.Properties
