module

meta import LynxTest.ProofAudit
import LynxTest.EmptyModule
-- These imports intentionally include private proof dependencies for the audit.
import all Lynx.Concurrent.Reduction
import all Lynx.Term.NativeTrace
import all Lynx.Term.NativeSchedule

namespace LynxTest.NativeAudit
open Lynx Concurrent

-- Preserve the upstream outcome explorer independently of the specialization.
private def referenceCheckFrom (accept : Outcome α → Bool) :
    Nat → List Key → Config α → Bool
  | 0, _, _ => false
  | depth + 1, sleep, config =>
      match config.steps with
      | [] =>
          match config.successors with
          | [] => accept config.outcome
          | successors => successors.all fun (_, next) => referenceCheckFrom accept depth [] next
      | steps =>
          match config.forced.bind fun key => steps.find? (·.1 == key) with
          | some (_, _, next) => referenceCheckFrom accept depth sleep next
          | none => explore (referenceCheckFrom accept depth) config.commutesWith sleep [] steps

/-- The specialization preserves every result of the upstream explorer,
including rejection, exhausted budgets, and arbitrary sleep sets. -/
theorem outcome_explorer_preserved (accept : Outcome α → Bool) (depth : Nat)
    (sleep : List Key) (config : Config α) :
    checkFrom accept depth sleep config = referenceCheckFrom accept depth sleep config := by
  unfold checkFrom
  induction depth generalizing sleep config with
  | zero => rfl
  | succ depth ih =>
    have recursive : checkStateFrom (fun last => accept last.outcome) depth =
        referenceCheckFrom accept depth := by
      funext sleep config
      exact ih sleep config
    simp only [checkStateFrom, referenceCheckFrom, recursive, Kernel.all_eq,
      Kernel.find?_eq]
    rfl

end LynxTest.NativeAudit

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Reduction
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeSchedule

-- Empty imported modules have no declarations, while unknown modules still fail.
run_cmd do
  let names ← LynxTest.ProofAudit.moduleDeclarations `LynxTest.EmptyModule
  unless names.isEmpty do throwError "expected an empty test module"
  LynxTest.ProofAudit.checkModule `LynxTest.EmptyModule

/-- error: unknown audit module: LynxTest.MissingAuditModule -/
#guard_msgs in
run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.MissingAuditModule

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.NativeAudit
