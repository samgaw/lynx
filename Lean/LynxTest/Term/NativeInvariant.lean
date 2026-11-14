module

import Lynx
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeInvariant
open Lynx Result

private def increments : Nat → Result Unit
  | 0 => .ok ()
  | count + 1 => .nativeModify (fun env => ((), {env with
      nativeRefCounter := env.nativeRefCounter + 1})) fun _ => increments count

theorem increments_preserve (count minimum : Nat) (env : Environment)
    (bounded : minimum ≤ env.nativeRefCounter) :
    NativeInvariant (fun state => minimum ≤ state.nativeRefCounter) (increments count) env := by
  induction count generalizing env with
  | zero => exact .ok _ _ _ bounded
  | succ count ih =>
      apply NativeInvariant.nativeModify _ _ _ bounded
      apply ih
      dsimp
      omega

theorem composed_preserve (first second minimum : Nat) (env : Environment)
    (bounded : minimum ≤ env.nativeRefCounter) :
    NativeInvariant (fun state => minimum ≤ state.nativeRefCounter)
      (increments first >>= fun _ => increments second) env := by
  have safe := increments_preserve first minimum env bounded
  apply safe.bind
  intro value middle completed
  exact increments_preserve second minimum middle (safe _ _ completed).1

/-- The composition theorem covers every finite raw prefix and keeps the
scheduler snapshot when a native operation blocks. -/
theorem composed_run (first second minimum : Nat) (env : Environment)
    (bounded : minimum ≤ env.nativeRefCounter) (elapsed : PID → Nat → Nat)
    (executed : Concurrent.Run
      (.start env (increments first >>= fun _ => increments second) elapsed) events last) :
    ∃ state, minimum ≤ state.nativeRefCounter ∧
      ((∃ residual, last = .start state residual elapsed) ∨
        ∃ residual, last = .running (Concurrent.State.initial state elapsed)
          [(state.currentPid, Concurrent.Task.root residual)] none false) :=
  (composed_preserve first second minimum env bounded).run elapsed executed

/-- Bind inversion retains the actual post-mutation environment supplied to the
continuation, even if the continuation subsequently changes it again. -/
theorem completed_bind_middle (before after : Environment) (next : Nat → Result α) (value : α)
    (trace : ReadyPrefix
      ((Result.nativeModify (fun env => (env.nativeRefCounter,
        {env with nativeRefCounter := env.nativeRefCounter + 1})) Result.ok) >>= next)
      before (.ok value) after) :
    ReadyPrefix (next before.nativeRefCounter)
      {before with nativeRefCounter := before.nativeRefCounter + 1} (.ok value) after := by
  obtain ⟨returned, middle, callee, continuation⟩ := trace.bind_returns
  have actual := callee.apply
  simp only [nativeModify_apply, ok_apply, Prod.mk.injEq, Outcome.ok.injEq] at actual
  obtain ⟨rfl, rfl⟩ := actual
  exact continuation

/-- Successful raw native runs retain the exact successful local execution,
so postconditions can observe its final environment without choosing a script. -/
theorem composed_success (first second minimum : Nat) (env : Environment)
    (bounded : minimum ≤ env.nativeRefCounter) (elapsed : PID → Nat → Nat)
    (executed : Concurrent.Run
      (.start env (increments first >>= fun _ => increments second) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok ())) :
    ∃ world, minimum ≤ world.nativeRefCounter ∧
      ReadyPrefix (increments first >>= fun _ => increments second) env (.ok ()) world ∧
      last = .start world (.ok ()) elapsed := by
  have safe := composed_preserve first second minimum env bounded
  obtain ⟨world, trace, ending⟩ := safe.run_returns elapsed executed terminal
  exact ⟨world, (safe _ _ trace).1, trace, ending⟩

private def transient : Result Term :=
  .nativeSet {nativeRefCounter := 7} (.nativeSet {} (.ok .true))

theorem transient_rejected : ¬ NativeInvariant (fun env => env.nativeRefCounter = 0) transient {} := by
  intro safe
  have trace : ReadyPrefix transient {} (.nativeSet {} (.ok .true)) {nativeRefCounter := 7} :=
    .nativeSet _ _ _ _ _ (.refl _ _)
  have impossible := (safe _ _ trace).1
  contradiction

private def pending : Result Term := .wait (fun _ => none) fun _ : Unit => .ok .true

theorem pending_preserves (env : Environment) :
    NativeInvariant (fun state => state.nativeHeap = env.nativeHeap) pending env := by
  apply NativeInvariant.wait (holds := fun state => state.nativeHeap = env.nativeHeap) _ _ env rfl
  intro reply updated impossible
  contradiction

theorem pending_not_success (elapsed : PID → Nat → Nat) :
    Concurrent.check Outcome.isTrue 4 (.start {} pending elapsed) = false := by cbv

/-- An unavailable native operation cannot acquire a successful-return witness
by entering the blocked scheduler snapshot. -/
theorem pending_never_succeeds (env : Environment) (elapsed : PID → Nat → Nat) (value : Term)
    (executed : Concurrent.Run (.start env pending elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok value)) : False := by
  obtain ⟨world, trace, _⟩ := (pending_preserves env).run_returns elapsed executed terminal
  cases trace with
  | wait _ _ _ _ _ _ _ impossible _ => contradiction

theorem scheduler_boundary_rejected :
    ¬ NativeInvariant (fun _ => True) (Result.schedule {} (.ok .nil) fun _ => .ok Term.true) {} := by
  intro safe
  exact (safe _ _ (.refl _ _)).2

end LynxTest.Term.NativeInvariant

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeInvariant
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeInvariant
