module

public import Init.Data.Ord.String
public import Lynx.Term.Compare
import all Init.Data.Ord.String

/-! Rules that let `cbv` evaluate closed programs. -/

public section

namespace Lynx.Term

attribute [cbv_eval] compare_self compare_atoms compare_reference compare_integers
  exactCompare_self exactCompare_atoms exactCompare_reference exactCompare_integers
  compare_tuple exactCompare_tuple compare_cons exactCompare_cons

/-- Atoms compare by name. Core implements string comparison natively, so
evaluation uses its definition through the order on strings. -/
@[cbv_eval] theorem string_compare_eq (left right : String) :
    String.compare left right = compareOfLessAndEq left right := by
  unfold String.compare
  rfl

end Lynx.Term
