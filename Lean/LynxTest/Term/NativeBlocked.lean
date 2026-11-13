module

import Lynx.Term.NativeTrace.Blocked
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeBlocked

open Lynx

private def acquire (env : Environment) : Option (Nat × Environment) :=
  if env.nativeHeap.isEmpty then
    some (env.nativeRefCounter, {env with nativeHeap := [(1, "owner", .pid env.currentPid)]})
  else none

private def tick (value : Nat) (env : Environment) : Option (Unit × Environment) :=
  match env.nativeHeap with
  | [(1, "owner", .pid owner)] =>
      if owner == env.currentPid then some ((), {env with nativeRefCounter := value + 1}) else none
  | _ => none

private def stopped : Result Term := .wait (fun _ => none) (fun _ : Unit => .ok (.atom "finished"))
private def stall (value : Nat) : Result Term := .wait (tick value) fun _ => stopped

private def program : Result Term :=
  .schedule {} (.wait acquire stall) fun _ => .wait acquire stall

private theorem stalled_trace (pid peer : PID) (value : Nat) :
    Result.ExclusiveBlocked pid peer acquire (stall value) (value, [(1, "owner", .pid pid)])
      (value + 1, [(1, "owner", .pid pid)]) := by
  refine .wait _ _ () _ (value + 1, [(1, "owner", .pid pid)]) _ ?_ ?_ ?_
  · intro env owner _ heap
    cases env
    simp_all [tick]
  · intro env _ _ heap
    simp [acquire, heap]
  · refine .blocked _ _ _ ?_ ?_
    · intro env _ _ _
      rfl
    · intro env _ _ heap
      simp [acquire, heap]

/-- Every finite preference stream observes a blocked owner snapshot after the
actual ready update, rather than assuming a favored pair of schedules. -/
theorem blocked_snapshots (counter : Nat) (choices : List ScheduleChoice) :
    let observed := program.run {nativeRefCounter := counter} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
      (.deadlock, counter + 1, [(1, "owner", .pid [])]) ∨
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
      (.deadlock, counter + 1, [(1, "owner", .pid [1])]) := by
  exact Result.two_wait_blocked_orders acquire stall acquire stall counter counter
    (counter, []) (counter, [(1, "owner", .pid [])]) (counter + 1, [(1, "owner", .pid [])])
    (counter, [(1, "owner", .pid [1])]) (counter + 1, [(1, "owner", .pid [1])])
    (by intro env owner count heap; cases env; simp_all [acquire])
    (by intro env owner count heap; cases env; simp_all [acquire])
    (stalled_trace [] [1] counter) (stalled_trace [1] [] counter) choices

/-- Blocking does not roll back the owner's already executed native update. -/
theorem blocked_preserves_update (counter : Nat) (choices : List ScheduleChoice) :
    (program.run {nativeRefCounter := counter} choices).2.nativeRefCounter = counter + 1 := by
  rcases blocked_snapshots counter choices with branch | branch <;>
    exact congrArg (fun snapshot => snapshot.2.1) branch

/-- Pending native work cannot be reported as a successful return. -/
theorem blocked_not_successful (counter : Nat) (choices : List ScheduleChoice) (value : Term) :
    (program.run {nativeRefCounter := counter} choices).1 ≠ .ok value := by
  have stuck : (program.run {nativeRefCounter := counter} choices).1 = .deadlock := by
    rcases blocked_snapshots counter choices with branch | branch <;>
      exact congrArg Prod.fst branch
  simp [stuck]

end LynxTest.Term.NativeBlocked

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Blocked
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeBlocked
