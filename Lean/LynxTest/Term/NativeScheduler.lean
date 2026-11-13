module

import Lynx.Concurrent.Confluence
import Lynx.Term.NativeTrace.Scheduled
-- Inspect the private executor while auditing its native scheduling boundaries.
import all Lynx.Term.Runner
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeScheduler

open Lynx Lynx.Concurrent

private def increment : Result Nat :=
  .nativeModify (fun env =>
    (env.nativeRefCounter + 1, { env with nativeRefCounter := env.nativeRefCounter + 1 })) .ok

private def accepts (expected : Nat) : Config Nat → Bool
  | .start env (.ok returned) _ => returned == expected && env.nativeRefCounter == expected
  | _ => false

/-- The actual native transition and its result agree for every initial counter. -/
theorem increment_checked (env : Environment) (elapsed : PID → Nat → Nat) :
    checkPost (accepts (env.nativeRefCounter + 1)) 2 (.start env increment elapsed) = true := by
  simp [checkPost, Config.successors, increment, accepts, isRequest]

/-- The check establishes the terminal-state property for every run. -/
theorem increment_every_run (env : Environment) (elapsed : PID → Nat → Nat)
    {events : List Event} {last : Config Nat} {outcome : Outcome Nat}
    (run : Run (.start env increment elapsed) events last) (terminal : Terminal last outcome) :
    accepts (env.nativeRefCounter + 1) last = true :=
  checkPost_sound (increment_checked env elapsed) run terminal

/-- The prefix interface proves the actual native computation's result for all
runs, independently of the terminal-state checker. -/
theorem increment_prefix_every_run (env : Environment) (elapsed : PID → Nat → Nat)
    {events : List Event} {last : Config Nat} {outcome : Outcome Nat}
    (run : Run (.start env increment elapsed) events last) (terminal : Terminal last outcome) :
    outcome = .ok (env.nativeRefCounter + 1) := by
  have trace : Result.ReadyPrefix increment env (.ok (env.nativeRefCounter + 1))
      { env with nativeRefCounter := env.nativeRefCounter + 1 } :=
    .nativeModify _ _ _ _ _ _ _ rfl (.refl _ _)
  exact trace.returns elapsed run terminal

/-- A source trace advances its own task within an arbitrary surrounding task
list, retaining the actual scheduler state and every peer task. -/
theorem increment_scheduled (state : State) (pid : PID)
    (before after : List (PID × Concurrent.Task Nat)) :
    ∃ events, Run
      (.running state (before ++ (pid, Concurrent.Task.root increment) :: after) none false)
      events
      (.running {state with nativeRefCounter := state.nativeRefCounter + 1}
        (before ++ (pid, Concurrent.Task.root (.ok (state.nativeRefCounter + 1))) :: after) none false) := by
  have trace : Result.SharedSteps pid increment (state.nativeRefCounter, state.nativeHeap)
      (state.nativeRefCounter + 1) (state.nativeRefCounter + 1, state.nativeHeap) := by
    refine .modify _ _ _ _ _ _ _ ?_ (.done _ _)
    intro env _ counter heap
    simp [counter, heap]
  simpa only [Concurrent.Task.root] using
    trace.scheduledRun state before after some none false rfl rfl

private def pendingRead : Result Nat := .wait (fun _ => none) (fun _ : Unit => .ok 1)

private def registerThenWait : Result Nat :=
  .nativeModify (fun env => ((), {env with nativeResourceTypes := ["counter"]})) fun _ =>
    .nativeGet fun env =>
      if env.nativeResourceTypes = ["counter"] then pendingRead else .error .exhausted

/-- Registration and decoding advance inside the real task list, but reaching
a blocked wait leaves it intact rather than certifying successful completion. -/
theorem registered_prefix_retains_wait (state : State) (pid : PID)
    (before after : List (PID × Concurrent.Task Nat)) :
    ∃ events, Run
      (.running state (before ++ (pid, Concurrent.Task.root registerThenWait) :: after) none false)
      events
      (.running {state with nativeResourceTypes := ["counter"]}
        (before ++ (pid, Concurrent.Task.root pendingRead) :: after) none false) := by
  have trace : Result.RegisteredPrefix pid registerThenWait
      (state.nativeRefCounter, state.nativeHeap) state.nativeResourceTypes pendingRead
      (state.nativeRefCounter, state.nativeHeap) ["counter"] := by
    refine .modify _ _ () _ (state.nativeRefCounter, state.nativeHeap) _ _ ["counter"] _ _ ?_ ?_
    · intro env _ counter heap _
      simp [counter, heap]
    · refine .read _ pendingRead _ _ _ _ _ ?_ (.refl _ _ _)
      intro env _ _ _ registered
      simp [registered]
  simpa only [Concurrent.Task.root] using
    trace.scheduledRun state before after some none false rfl rfl rfl

/-- A blocked native residual has no own step, even alongside runnable peers. -/
theorem registered_residual_is_blocked (state : State) (pid : PID) :
    (Concurrent.Task.root pendingRead).own state pid = [] := by
  simp [Concurrent.Task.root, Concurrent.Task.own, pendingRead]

/-- An unchanged-counter claim is rejected, rather than assumed by the checker. -/
theorem rejects_wrong_counter (env : Environment) (elapsed : PID → Nat → Nat) :
    checkPost (accepts env.nativeRefCounter) 2 (.start env increment elapsed) = false := by
  simp [checkPost, Config.successors, increment, accepts, isRequest]

/-- Reaching the next state without enough fuel does not establish its property. -/
theorem rejects_short_budget (env : Environment) (elapsed : PID → Nat → Nat) :
    checkPost (accepts (env.nativeRefCounter + 1)) 1 (.start env increment elapsed) = false := by
  simp [checkPost, Config.successors, increment]

/-- A blocked native operation retains the whole environment and cannot succeed
by consuming scheduler choices. -/
theorem blocked_keeps_state (env : Environment) (choices : List ScheduleChoice) :
    (Result.wait (β := Unit) (fun _ => none) (fun _ => Result.ok true)).run env choices =
      (.deadlock, env) :=
  Result.wait_blocked_run _ _ env rfl choices

private def yieldedRead : Result Nat :=
  Result.schedule {} (.nativeSet { nativeRefCounter := 7 } (.ok .nil)) fun _ =>
    .wait (fun env => some ((), env)) fun _ =>
      .nativeGet fun env => .ok env.nativeRefCounter

/-- A successful native wait remains a scheduling boundary. The second choice
runs the child before the root reads the shared state. -/
theorem ready_wait_yields :
    (yieldedRead.run {} [.current, .swap [1]]).1 = .ok 7 := by
  cbv

/-- An atomic native modification retains local execution. It cannot consume
a later choice merely because native waits yield. -/
theorem atomic_native_modification_stays_local :
    ((Result.schedule {} (.nativeSet { nativeRefCounter := 7 } (.ok .nil)) fun _ =>
      .nativeModify (fun env => ((), env)) fun _ =>
        .nativeGet fun env => .ok env.nativeRefCounter).run {} [.current, .swap [1]]).1 = .ok 0 := by
  cbv

/-- Replacing native state preserves the independently scheduled state. -/
theorem native_frame (state : State) (native : NativeState) :
    (state.withNative native).native = native ∧
    (state.withNative native).processes = state.processes ∧
    (state.withNative native).timers = state.timers ∧
    (state.withNative native).inTransit = state.inTransit ∧
    (state.withNative native).elapsed = state.elapsed := by
  simp

/-- Replacing an integer cell by a floating-point cell is an observable write,
even if Erlang's numeric comparison would call their values equal. -/
theorem distinguishes_native_cell_representation :
    NativeState.identical
      { refCounter := 0, heap := [(0, "value", .integer 1)], resourceTypes := [], finalizerMode := .unspecified }
      { refCounter := 0, heap := [(0, "value", .float ⟨false, 1023, 0⟩)], resourceTypes := [], finalizerMode := .unspecified } = false := by
  decide

/-- Every shared native component participates in dependency checking. -/
theorem native_writes_are_observed :
    let observes : Observes := { native := true }
    let state : State := {}
    Effect.keepsQueues { native := some fun native => { native with refCounter := 1 } } observes state = false ∧
    Effect.keepsQueues { native := some fun native => { native with heap := [(0, "value", .nil)] } }
      observes state = false ∧
    Effect.keepsQueues { native := some fun native => { native with resourceTypes := ["resource"] } }
      observes state = false ∧
    Effect.keepsQueues { native := some fun native => { native with finalizerMode := .deferred } }
      observes state = false := by
  decide

/-- Two writes of different snapshots cannot be reordered as independent steps. -/
theorem conflicting_native_writes_do_not_commute :
    Effect.commutesQueues
      { native := some fun native => { native with refCounter := 1 } }
      { native := some fun native => { native with refCounter := 2 } } {} = false := by
  decide

/-- A getter depends on a peer's native write, even when their process records
are disjoint. -/
theorem native_read_write_dependency :
    let state := State.initial ({} : Environment)
    let reader : Concurrent.Task Nat := Concurrent.Task.root (.nativeGet fun env => .ok env.nativeRefCounter)
    let writer : Concurrent.Task Nat := Concurrent.Task.root (.nativeSet { nativeRefCounter := 1 } (.ok 1))
    (reader.footprint state []).independent (writer.footprint state [1]) state = false := by
  decide

/- The complete reduction and confluence modules retain the normal axiom policy,
including their private commutation and transition-matching proofs. -/
run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Scheduled
  LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Footprint
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Reduction
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Confluence

end LynxTest.Term.NativeScheduler

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeScheduler
