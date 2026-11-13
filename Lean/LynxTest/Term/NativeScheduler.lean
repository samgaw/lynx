module

import Lynx.Concurrent.Confluence
import Lynx.Term.NativeTrace
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
    Effect.keeps { native := some fun native => { native with refCounter := 1 } } observes state = false ∧
    Effect.keeps { native := some fun native => { native with heap := [(0, "value", .nil)] } }
      observes state = false ∧
    Effect.keeps { native := some fun native => { native with resourceTypes := ["resource"] } }
      observes state = false ∧
    Effect.keeps { native := some fun native => { native with finalizerMode := .deferred } }
      observes state = false := by
  decide

/-- Two writes of different snapshots cannot be reordered as independent steps. -/
theorem conflicting_native_writes_do_not_commute :
    Effect.commutes
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
  LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Footprint
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Reduction
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent.Confluence

end LynxTest.Term.NativeScheduler

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeScheduler
