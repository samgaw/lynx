module

public meta import Lean

/-! Opt-in, proof-producing arithmetic for symbolic native runtime evaluation.
Ground comparisons use ordinary evaluation. Symbolic natural comparisons are
rewritten only when Lean's arithmetic tactic proves their Boolean result. -/

public section
namespace Lynx.NativeArithmetic

open Lean Meta Elab

private meta def proveComparison (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if !e.hasFVar then return none
  for value in [true, false] do
    let saved ← saveState
    try
      let rhs := toExpr value
      let args := e.getAppArgs
      let proposition ← if e.isAppOfArity ``Nat.beq 2 then mkEq args[0]! args[1]!
        else mkAppM ``LE.le #[args[0]!, args[1]!]
      let comparison ← mkDecide proposition
      let goal ← mkFreshExprSyntheticOpaqueMVar (← mkEq comparison rhs)
      let (goals, _) ← Elab.runTactic goal.mvarId!
        (← `(tactic| (simp only [Bool.eq_false_iff, ne_eq, decide_eq_true_eq]; omega)))
        (ctx := {errToSorry := false})
      if goals.isEmpty then return some (rhs, ← instantiateMVars goal)
    catch _ => pure ()
    saved.restore
  return none

/-- Resolve symbolic natural order comparisons using kernel-checked arithmetic. -/
scoped cbv_simproc cbv_eval arithmeticCompare (Nat.ble _ _) := fun e => do
  let some (rhs, proof) ← proveComparison e | return .rfl
  return .step rhs proof

/-- Resolve symbolic natural identity comparisons using kernel-checked arithmetic. -/
scoped cbv_simproc cbv_eval arithmeticEqual (Nat.beq _ _) := fun e => do
  let some (rhs, proof) ← proveComparison e | return .rfl
  return .step rhs proof

end Lynx.NativeArithmetic
