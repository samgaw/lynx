module
import Lynx
import Lynx.Rustler
meta import LynxTest.ProofAudit

namespace LynxTest.Term.ReadyPrefix
open Lynx

private def advance (value : Nat) (env : Environment) : Option (Nat × Environment) :=
  some (value,{env with nativeRefCounter := env.nativeRefCounter + value})

private def program : Result Nat := do
  let first ← Result.wait (advance 2) .ok
  let second ← Result.wait (advance 3) .ok
  .ok (first + second)

theorem actual_first_wait (env : Environment) :
    Result.ReadyPrefix program env
      (Result.wait (advance 3) fun second => .ok (2 + second))
      {env with nativeRefCounter := env.nativeRefCounter + 2} := by
  simp only [program,Result.wait_bind,Result.ok_bind]
  exact .wait _ _ 2 _ _ _ _ rfl (.refl _ _)

theorem prefix_preserves_execution (env : Environment) :
    program env = (.ok 5,{env with nativeRefCounter := env.nativeRefCounter + 2 + 3}) := by
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
      {env with nativeRefCounter := env.nativeRefCounter + 2} :=
  (actual_first_wait env).bind _

private def stateful : Result Nat := .nativeGet fun env =>
  .nativeSet {env with nativeRefCounter := env.nativeRefCounter + 1} program

theorem state_transition (env : Environment) :
    Result.ReadyPrefix stateful env program {env with nativeRefCounter := env.nativeRefCounter + 1} := by
  exact .nativeGet _ _ _ _ (.nativeSet _ _ _ _ _ (.refl _ _))

theorem state_transition_agrees (env : Environment) :
    stateful env = program {env with nativeRefCounter := env.nativeRefCounter + 1} :=
  (state_transition env).apply

theorem stateful_caller (env : Environment) :
    Result.ReadyPrefix (stateful >>= fun value => .ok (value + 1)) env
      (program >>= fun value => .ok (value + 1)) {env with nativeRefCounter := env.nativeRefCounter + 1} :=
  (state_transition env).bind _

theorem adapter_preserves_state_transition (env : Environment) :
    Result.ReadyPrefix (Rustler.executeNative stateful (fun n => .integer n)) env
      (Rustler.executeNative program (fun n => .integer n)) {env with nativeRefCounter := env.nativeRefCounter + 1} :=
  Rustler.executeNative_readyPrefix (state_transition env) _

private def failing (exception : Exception) : Result Nat := .nativeGet fun env =>
  .nativeSet {env with nativeRefCounter := env.nativeRefCounter + 1}
    (.wait (advance 2) fun _ => .error exception)

private theorem failure_prefix (exception : Exception) (env : Environment) :
    Result.ReadyPrefix (failing exception) env (.error exception)
      {env with nativeRefCounter := env.nativeRefCounter + 1 + 2} := by
  exact .nativeGet _ _ _ _ (.nativeSet _ _ _ _ _ (.wait _ _ _ _ _ _ _ rfl (.refl _ _)))

private def observe (_ : Exception) : Result Nat := .nativeGet fun env => .ok env.nativeRefCounter

theorem handler_observes_updated_state (env : Environment) :
    Result.handle (failing (.error (.atom "failed"))) observe env =
      (.ok (env.nativeRefCounter + 1 + 2), {env with nativeRefCounter := env.nativeRefCounter + 1 + 2}) := by
  rw [((failure_prefix _ env).handle observe).apply]
  simp [Result.handle,observe]

theorem try_observes_updated_state (env : Environment) :
    Result.tryWith (failing (.error (.atom "failed"))) (fun n => .ok (n + 1)) observe env =
      (.ok (env.nativeRefCounter + 1 + 2), {env with nativeRefCounter := env.nativeRefCounter + 1 + 2}) := by
  rw [((failure_prefix _ env).tryWith _ observe).apply]
  simp [observe]

theorem exhaustion_is_not_caught (env : Environment) :
    Result.tryWith (failing .exhausted) (fun n => .ok (n + 1)) observe env =
      (.error .exhausted, {env with nativeRefCounter := env.nativeRefCounter + 1 + 2}) := by
  rw [((failure_prefix _ env).tryWith _ observe).apply]
  simp only [Result.tryWith_exhausted,Result.error_apply]

end LynxTest.Term.ReadyPrefix
run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.ReadyPrefix
