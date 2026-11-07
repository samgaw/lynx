module
import Lynx
import Lynx.Rustler
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

private def stateful : Result Nat := .get fun env =>
  .set {env with refCounter := env.refCounter + 1} program

theorem state_transition (env : Environment) :
    Result.ReadyPrefix stateful env program {env with refCounter := env.refCounter + 1} := by
  exact .get _ _ _ _ (.set _ _ _ _ _ (.refl _ _))

theorem state_transition_agrees (env : Environment) :
    stateful env = program {env with refCounter := env.refCounter + 1} :=
  (state_transition env).apply

theorem stateful_caller (env : Environment) :
    Result.ReadyPrefix (stateful >>= fun value => .ok (value + 1)) env
      (program >>= fun value => .ok (value + 1)) {env with refCounter := env.refCounter + 1} :=
  (state_transition env).bind _

theorem adapter_preserves_state_transition (env : Environment) :
    Result.ReadyPrefix (Rustler.executeNative stateful (fun n => .integer n)) env
      (Rustler.executeNative program (fun n => .integer n)) {env with refCounter := env.refCounter + 1} :=
  Rustler.executeNative_readyPrefix (state_transition env) _

end LynxTest.Term.ReadyPrefix
run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.ReadyPrefix
