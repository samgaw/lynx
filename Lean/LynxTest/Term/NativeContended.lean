module

import Lynx.Term.NativeTrace.Contended
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeContended

open Lynx

private def acquire (env : Environment) : Option (Nat × Environment) :=
  if env.nativeHeap.isEmpty then
    some (env.nativeRefCounter, {env with nativeHeap := [(1, "owner", .pid env.currentPid)]})
  else none

private def release (value : Nat) (env : Environment) : Option (Unit × Environment) :=
  match env.nativeHeap with
  | [(1, "owner", .pid owner)] =>
      if owner == env.currentPid then
        some ((), {env with nativeRefCounter := value + 1, nativeHeap := []}) else none
  | _ => none

private def critical (value : Nat) : Result Term :=
  .wait (release value) fun _ => .ok (.integer (value + 1))

private theorem critical_trace (pid : PID) (value : Nat) :
    Result.SharedSteps pid (critical value) (value, [(1, "owner", .pid pid)])
      (.integer (value + 1)) (value + 1, []) := by
  refine .wait _ _ () _ (value + 1, []) _ _ ?_ (.done _ _)
  intro env owner _ heap
  cases env
  simp_all [release]

/-- The peer's failed acquisition is followed by both real release callbacks.
This synthetic runtime regression covers the concrete contended schedule. -/
theorem contended_updates (counter : Nat) :
    (Result.schedule {} (.wait acquire critical) (fun _ => .wait acquire critical)).run
      {nativeRefCounter := counter} [.current, .swap [1]] =
      (.ok (.integer (counter + 1)), {nativeRefCounter := counter + 2}) := by
  exact Result.two_wait_interleave_steps acquire critical acquire critical
    counter (counter + 1) (.integer (counter + 1)) (.integer (counter + 2))
    (counter, []) (counter, [(1, "owner", .pid [])]) (counter + 1, [])
    (counter + 1, [(1, "owner", .pid [1])]) (counter + 2, [])
    (by simp [acquire]) (critical_trace [] counter) (by simp [acquire])
    (by simp [acquire]) (critical_trace [1] (counter + 1))

/-- A peer cannot commit the owner's release transition. -/
theorem peer_cannot_release (counter : Nat) :
    release counter {currentPid := [1], nativeHeap := [(1, "owner", .pid [])]} = none := by
  rfl

end LynxTest.Term.NativeContended

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Contended
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeContended
