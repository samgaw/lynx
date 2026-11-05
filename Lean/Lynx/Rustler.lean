module

public import Lynx.Term

public section

namespace Lynx.Rustler

/-- Rustler 0.38/0.39 accept only the atoms `true` and `false` as booleans. -/
@[expose] def decodeBool : Term → Except Exception Bool
  | .atom "true" => .ok true
  | .atom "false" => .ok false
  | _ => .error (.error (.atom "badarg"))

/-- Rustler encodes booleans as the corresponding Erlang atoms. -/
@[expose] def encodeBool (value : Bool) : Term :=
  if value then .atom "true" else .atom "false"

@[simp] theorem decodeBool_encodeBool (value : Bool) :
    decodeBool (encodeBool value) = .ok value := by
  cases value <;> rfl

end Lynx.Rustler
