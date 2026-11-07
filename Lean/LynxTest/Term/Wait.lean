module

import Lynx
-- This module audits the private scheduler and its structural progress proof.
import all Lynx.Term.Runner
meta import LynxTest.ProofAudit

namespace LynxTest.Term.Wait
open Lynx

/-- Waiting does not manufacture progress when the closed process tree is blocked. -/
theorem blocked_has_no_success :
    ((Result.wait (α := Term) (β := Unit) (fun _ => none) (fun _ => .ok (.atom "finished"))) {}).1 = .deadlock := by
  cbv

/-- Readiness does not consume or manufacture Erlang messages. -/
theorem blocked_preserves_mailbox :
    (Result.wait (α := Term) (β := Unit) (fun _ => none) (fun _ => .ok .nil))
      { currentProcess := { mailbox := [.atom "untouched"] } } =
      (.deadlock, { currentProcess := { mailbox := [.atom "untouched"] } }) := by cbv

private def published : Result Term :=
  .get fun env => .set { env with nativeHeap := [(1, "cell", .integer 7)] } (.ok .nil)

private def awaitValue : Result Term :=
  .wait (fun env => match env.nativeHeap with
    | [(_, _, value)] => some (value, env)
    | _ => none) .ok

/-- A blocked waiter resumes after another process changes shared state. -/
theorem state_change_wakes_waiter :
    (do let _ ← Result.schedule published .ok; awaitValue)
      { currentProcess := { mailbox := [.atom "untouched"] } } =
      (.ok (.integer 7), {
        pidCounter := 2
        nativeHeap := [(1, "cell", .integer 7)]
        currentProcess := { mailbox := [.atom "untouched"] }
      }) := by cbv

private def claim (env : Environment) : Option (Unit × Environment) :=
  if env.refCounter == 0 then some ((), { env with refCounter := 1 }) else none

private def compete : Result Term := do
  let _ ← Result.schedule (.wait claim fun _ => .ok .nil) .ok
  .wait claim fun _ => .ok .nil

/-- Readiness and the update are atomic: two ready requests cannot both claim. -/
theorem exactly_one_claim :
    (compete { schedule := [.current] }).1 = .deadlock ∧
    (compete { schedule := [.current] }).2.refCounter = 1 ∧
    (compete { schedule := [.swap 2] }).1 = .deadlock ∧
    (compete { schedule := [.swap 2] }).2.refCounter = 1 := by cbv

-- These synthetic polls isolate scheduler behavior. Rust implementation
-- correspondence is checked separately against actual extracted functions.
private def acquire (env : Environment) : Option (Nat × Environment) :=
  if env.nativeHeap.isEmpty then
    some (env.refCounter, { env with nativeHeap := [(1, "owner", .pid env.currentPid)] })
  else none

private def release (value : Nat) (env : Environment) : Option (Unit × Environment) :=
  match env.nativeHeap with
  | [(1, "owner", .pid owner)] =>
    if owner == env.currentPid then
      some ((), { env with nativeHeap := [], refCounter := value }) else none
  | _ => none

private def update : Result Term := do
  let value ← Result.wait acquire .ok
  Result.wait (release (value + 1)) fun _ => .ok .nil

private def updates : Result Term := do
  let _ ← Result.schedule update .ok
  update

/-- Releasing wakes a contending process without losing its protected update. -/
theorem contending_updates_complete :
    updates { schedule := [.current, .swap 2] } = (.ok .nil, { pidCounter := 2, refCounter := 2 }) ∧
    updates { schedule := [.swap 2, .swap 1] } = (.ok .nil, { pidCounter := 2, refCounter := 2 }) := by cbv

private def tick (env : Environment) : Option (Unit × Environment) :=
  some ((), {env with refCounter := env.refCounter + 1})

private def postUpdate (value : Nat) : Result Term :=
  .wait tick fun _ => .wait tick fun _ => .wait (release (value + 3)) fun _ => .ok .nil

private theorem update_trace (pid value : Nat) :
    Result.SharedSteps pid (postUpdate value) (value, [(1, "owner", .pid pid)]) .nil (value + 3, []) := by
  refine .wait _ _ () _ (value + 1, [(1, "owner", .pid pid)]) _ _ ?_ ?_
  · intro env owner counter heap
    simp [tick, counter, heap]
  · refine .wait _ _ () _ (value + 2, [(1, "owner", .pid pid)]) _ _ ?_ ?_
    · intro env owner counter heap
      simp [tick, counter, heap, Nat.add_assoc]
    · refine .wait _ _ () _ (value + 3, []) _ _ ?_ ?_
      · intro env owner counter heap
        simp [release, heap, owner]
      · exact .done Term.nil _

/-- Intermediate ready waits remain scheduler steps while a competitor blocks;
the same shared cells survive through both complete worker traces. -/
theorem contending_multi_wait_updates :
    (Result.schedule (.wait acquire postUpdate) (fun _ => .wait acquire postUpdate))
      {schedule := [.current, .swap 2]} =
      (.ok .nil, {pidCounter := 2, refCounter := 6}) := by
  exact Result.two_wait_interleave_steps acquire postUpdate acquire postUpdate 0 3 .nil .nil
    (0, []) (0, [(1, "owner", .pid 1)]) (3, []) (3, [(1, "owner", .pid 2)]) (6, [])
    (by simp [acquire]) (update_trace 1 0) (by simp [acquire])
    (by simp [acquire]) (update_trace 2 3)

/-- Poll readiness alone never makes the wait read-only or pure. -/
theorem wait_is_effectful (poll : Environment → Option (β × Environment)) (next : β → Result α) :
    ¬ Result.IsPure (.wait poll next) ∧ ¬ Result.IsReadOnly (.wait poll next) := by
  simp [Result.IsReadOnly]

end LynxTest.Term.Wait

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.Wait

run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
