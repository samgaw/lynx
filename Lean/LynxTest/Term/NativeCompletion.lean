module

import Lynx.Term.NativeTrace.Completion
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeCompletion

open Lynx

private def finish : Result Term :=
  .nativeModify (fun env =>
    ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) fun _ =>
      .wait (fun env => some ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) fun _ =>
        .ok (.atom "child")

private def write : Result Term := .nativeGet fun env =>
  .nativeSet {env with nativeRefCounter := env.nativeRefCounter + 1} finish

private def work : Result Term := .nativeGet fun _ => write

private theorem work_trace (counter : Nat) (heap : List (Nat × String × Term)) :
    Result.SharedSteps [1] work (counter, heap) (.atom "child") (counter + 3, heap) := by
  refine .read _ write _ _ _ (by intros; rfl) ?_
  refine .update _ finish _ (counter + 1, heap) _ _ ?_ ?_
  · intro env owner count stored
    simp [count, stored]
  · refine .modify _ _ () _ (counter + 2, heap) _ _ ?_ ?_
    · intro env owner count stored
      cases env
      simp_all [Nat.add_assoc]
    · refine .wait _ _ () _ (counter + 3, heap) _ _ ?_ (.done _ _)
      intro env owner count stored
      cases env
      simp_all [Nat.add_assoc]

/-- Every finite stream, including attempts to select absent processes, retains
all read/set, modify and ready-wait transitions of the actual child. -/
theorem all_choices (counter : Nat) (heap : List (Nat × String × Term))
    (rootValue : Term) (choices : List ScheduleChoice) :
    let observed := (Result.schedule {} work (fun _ => .ok rootValue)).run
      {nativeRefCounter := counter, nativeHeap := heap} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
      (.ok rootValue, counter + 3, heap) := by
  exact Result.two_completed_shared_choices work rootValue (.atom "child")
    (counter, heap) (counter + 3, heap) (work_trace counter heap) choices

/-- Completing the root cannot discard the later child writes. -/
theorem child_writes_survive (counter : Nat) (choices : List ScheduleChoice) :
    ((Result.schedule {} work (fun _ => .ok (Term.atom "root"))).run
      {nativeRefCounter := counter} choices).2.nativeRefCounter ≠ counter := by
  have changed := congrArg (fun observed => observed.2.1) (all_choices counter [] (Term.atom "root") choices)
  simp only at changed
  omega

/-- The child's final value cannot replace the root's result. -/
theorem child_cannot_replace_root (counter : Nat) (choices : List ScheduleChoice) :
    ((Result.schedule {} work (fun _ => .ok (Term.atom "root"))).run
      {nativeRefCounter := counter} choices).1 ≠ .ok (Term.atom "child") := by
  have returned := congrArg Prod.fst (all_choices counter [] (Term.atom "root") choices)
  simp only at returned
  rw [returned]
  intro equal
  have impossible := congrArg (fun result : Outcome Term =>
    match result with | .ok (.atom name) => name | _ => "") equal
  exact (by decide : "root" ≠ "child") impossible

end LynxTest.Term.NativeCompletion

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Completion
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeCompletion
