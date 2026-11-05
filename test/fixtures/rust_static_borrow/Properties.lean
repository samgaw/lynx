module
public import Nested.Extraction.Funs
public section
open Aeneas Aeneas.Std nested_static
namespace Nested

theorem preserves_string (message : Str) : extract (.Text message) = .ok (some message) := by
  simp [extract, shared]

theorem empty_result : extract .Empty = .ok none := by
  simp [extract]

theorem detects_text (value : Borrowed) : nested value =
    .ok (match value with | .Text _ => true | .Empty => false) := by
  cases value <;> simp [nested, shared]
end Nested
