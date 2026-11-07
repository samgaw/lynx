module
import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Term.ReadyPrefix
open Lynx

private def advance (value : Nat) (env : Environment) : Option (Nat × Environment) :=
  some (value,{env with refCounter := env.refCounter + value})

private def program : Result Nat := do
  let first ← Result.wait (advance 2) .ok
  let second ← Result.wait (advance 3) .ok
  .ok (first + second)

theorem actual_first_wait (env : Environment) :
    Result.ReadyPrefix program env
      (Result.wait (advance 3) fun second => .ok (2 + second))
      {env with refCounter := env.refCounter + 2} := by
  simp only [program,Result.wait_bind,Result.ok_bind]
  exact .wait _ _ 2 _ _ _ _ rfl (.refl _ _)

theorem prefix_preserves_execution (env : Environment) :
    program env = (.ok 5,{env with refCounter := env.refCounter + 2 + 3}) := by
  rw [Result.ReadyPrefix.apply (actual_first_wait env)]
  rw [Result.wait_ready_apply _ _ _ _ _ (by rfl)]
  simp

theorem blocked_cannot_advance (env after : Environment) (residual : Result Nat)
    (trace : Result.ReadyPrefix (.wait (β := Unit) (fun _ => none) (fun _ => .ok 1)) env residual after) :
    after = env := by
  cases trace with
  | refl => rfl
  | wait poll next reply before middle residual after ready rest => cases ready

theorem caller_continuation (env : Environment) :
    Result.ReadyPrefix (program >>= fun value => .ok (value + 1)) env
      ((Result.wait (advance 3) fun second => .ok (2 + second)) >>= fun value => .ok (value + 1))
      {env with refCounter := env.refCounter + 2} :=
  (actual_first_wait env).bind _

end LynxTest.Term.ReadyPrefix
run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.ReadyPrefix
