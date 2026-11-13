module

import Lynx.Term.NativeTrace.Orders
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeOrders

open Lynx

private def held (pid : PID) : List (Nat × String × Term) := [(1, "mutex", .pid pid)]

private def acquire (env : Environment) : Option (Nat × Environment) :=
  match env.nativeHeap with
  | [] => some (env.nativeRefCounter, {env with nativeHeap := held env.currentPid})
  | _ => none

private def release (value : Nat) : Result Term :=
  .wait (fun env => some ((), env)) fun _ =>
    .nativeModify (fun env => ((), {env with nativeHeap := []})) fun _ => .ok (.integer value)

private def update (value : Nat) : Result Term := .nativeGet fun env =>
  .nativeSet {env with nativeRefCounter := value + 1} (release value)

private def critical (value : Nat) : Result Term := .nativeGet fun _ => update value
private def worker : Result Term := .wait acquire critical
private def program : Result Term := .schedule {} worker fun _ => worker

private theorem excluded (pid peer : PID) (counter : Nat) :
    ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = counter →
      env.nativeHeap = held pid → acquire env = none := by
  intro env _ _ stored
  simp [acquire, stored, held]

private theorem critical_trace (pid peer : PID) (counter : Nat) :
    Result.ExclusiveSteps pid peer acquire (critical counter) (counter, held pid)
      (.integer counter) (counter + 1, []) := by
  refine .read _ (update counter) _ _ _ (by intros; rfl) (excluded pid peer counter) ?_
  refine .update _ (release counter) _ (counter + 1, held pid) _ _ ?_ (excluded pid peer counter) ?_
  · intro env owner count stored
    simp only [update, stored]
  · refine .wait _ _ () _ (counter + 1, held pid) _ _ ?_ (excluded pid peer (counter + 1)) ?_
    · intro env owner count stored
      cases env
      simp_all
    · refine .modify _ _ () _ (counter + 1, []) _ _ ?_ (excluded pid peer (counter + 1)) (.done _ _)
      intro env owner count stored
      cases env
      simp_all

private theorem worker_trace (pid peer : PID) (counter : Nat) :
    Result.SharedSteps pid worker (counter, []) (.integer counter) (counter + 1, []) := by
  refine .wait _ _ counter _ (counter, held pid) _ _ ?_ (critical_trace pid peer counter).ready
  intro env owner count stored
  cases env
  simp_all [acquire]

/-- Both initially ready workers execute their actual critical sections. Every
finite scheduler stream yields one of the two real acquisition-order results. -/
theorem serial_orders (counter : Nat) (choices : List ScheduleChoice) :
    let observed := program.run {nativeRefCounter := counter} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
        (.ok (.integer counter), counter + 2, []) ∨
      (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
        (.ok (.integer (counter + 1)), counter + 2, []) := by
  exact Result.two_wait_serial_orders acquire critical acquire critical
    counter counter (.integer counter) (.integer counter) (.integer (counter + 1)) (.integer (counter + 1))
    (counter, []) (counter, held []) (counter + 1, []) (counter + 2, [])
    (counter, held [1]) (counter + 1, []) (counter + 2, [])
    (by intro env owner count stored; cases env; simp_all [acquire])
    (by intro env owner count stored; cases env; simp_all [acquire])
    (critical_trace [] [1] counter) (worker_trace [1] [] (counter + 1))
    (critical_trace [1] [] counter) (worker_trace [] [1] (counter + 1)) choices

/-- Neither acquisition order can lose the second increment. -/
theorem both_writes_survive (counter : Nat) (choices : List ScheduleChoice) :
    (program.run {nativeRefCounter := counter} choices).2.nativeRefCounter = counter + 2 := by
  rcases serial_orders counter choices with branch | branch <;>
    exact congrArg (fun observed => observed.2.1) branch

/-- Successful completion releases the actual shared mutex cell. -/
theorem no_mutex_left_held (counter : Nat) (choices : List ScheduleChoice) :
    (program.run {nativeRefCounter := counter} choices).2.nativeHeap = [] := by
  rcases serial_orders counter choices with branch | branch <;>
    exact congrArg (fun observed => observed.2.2) branch

end LynxTest.Term.NativeOrders

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Orders
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeOrders
