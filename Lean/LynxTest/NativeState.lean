module

import Lynx
import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit

namespace LynxTest.NativeState
open Lynx

private def prefixIncrement : Result Nat :=
  .nativeModify (fun env => ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) fun _ =>
    .nativeGet fun env => .ok env.nativeRefCounter

/-- Ordinary public imports can lift actual native modification/read traces to
all-run properties for arbitrary admitted environments. -/
theorem native_prefix_every_run (initial : Environment) :
    concurrentFrom initial prefixIncrement (.ok (initial.nativeRefCounter + 1)) := by
  apply concurrentFrom_of_readyPrefix
  exact .nativeModify _ _ () initial _ _ _ rfl (.nativeGet _ _ _ _ (.refl _ _))

/-- A contradictory result cannot be certified by the all-run native interface. -/
theorem native_prefix_unchanged_rejected (initial : Environment) :
    ¬ concurrentFrom initial prefixIncrement (.ok initial.nativeRefCounter) := by
  intro unchanged
  obtain ⟨events, last, run, terminal⟩ := Result.run_reaches prefixIncrement initial []
  have returned := native_prefix_every_run initial (fun _ _ => 0) events last _ run terminal
  have wrong := unchanged (fun _ _ => 0) events last _ run terminal
  have incompatible := congrArg
    (fun result : Outcome Nat => match result with | .ok value => value | _ => 0)
    (returned.symm.trans wrong)
  simp only at incompatible
  omega

private def sharedUpdate : Result :=
  Result.schedule {} (.nativeSet {nativeRefCounter := 7} (.ok .nil)) fun _ =>
    .wait (fun env => if env.nativeRefCounter = 7 then some ((), env) else none) fun _ =>
      .nativeGet fun env => .ok (.integer env.nativeRefCounter)

/-- A native write made by a child is visible to the parent under every schedule. -/
theorem sharedUpdate_every_schedule :
    concurrent sharedUpdate (.ok (.integer 7)) := by
  refine concurrent_of_check sharedUpdate
    (fun | .ok (.integer 7) => true | _ => false) 16 (by intro elapsed; cbv) ?_
  intro result accepted
  split at accepted
  · rfl
  · contradiction

private def atomicIncrement : Result Unit :=
  .nativeModify (fun env => ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) .ok

private def concurrentIncrements : Result :=
  Result.schedule {} (do
    atomicIncrement
    Result.send [] .nil (.ok .nil)) fun _ => do
      atomicIncrement
      Result.receive .infinity (fun _ message => some message) fun _ =>
        .nativeGet fun env => .ok (.integer env.nativeRefCounter)

/-- A synchronous native transition retains every concurrent update. -/
theorem atomic_updates_every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.integer 2) => true | _ => false) 20
      (.start {} concurrentIncrements elapsed) = true := by cbv

/-- A synchronous native transition preserves the caller's scheduling stream. -/
theorem atomic_transition_run (transition : Environment → β × Environment)
    (next : β → Result α) (env : Environment) (choices : List ScheduleChoice) :
    (Result.nativeModify transition next).run env choices =
      (next (transition env).1).run (transition env).2 choices :=
  Result.nativeModify_run transition next env choices

private def finishesWithCounter : Result :=
  Result.schedule {} (do atomicIncrement; .ok .nil) fun _ => do
    atomicIncrement
    .ok .true

private def terminalCounter (expected : Nat) (config : Concurrent.Config Term) : Bool :=
  let correct := match config with
    | .start env _ _ => env.nativeRefCounter == expected
    | .running state .. => state.nativeRefCounter == expected
  match config.outcome with
    | .ok (.atom "true") => correct
    | _ => false

/-- The root returns only a boolean; the checked postcondition additionally
observes the final shared state after both workers have finished. -/
theorem terminal_shared_counter_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (terminalCounter 2) 20 (.start {} finishesWithCounter elapsed) = true := by cbv

theorem terminal_shared_counter_every_run (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start {} finishesWithCounter elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) : terminalCounter 2 last = true :=
  Concurrent.checkPost_sound (terminal_shared_counter_checked elapsed) run terminal

theorem wrong_terminal_shared_counter_rejected (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (terminalCounter 1) 20 (.start {} finishesWithCounter elapsed) = false := by cbv

theorem exhausted_postcondition_budget_rejected (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (fun _ => true) 0 (.start {} finishesWithCounter elapsed) = false := rfl

private def sharedFinalizerPolicy : Result :=
  Result.schedule {} (do
    atomicIncrement
    .nativeGet fun env =>
      Result.send [] (match env.nativeFinalizerMode with
        | .deferred => Term.true | _ => Term.false) (.ok .nil)) fun _ => do
    atomicIncrement
    Result.receive .infinity (fun _ message => some message) fun message =>
      .ok (message.getD Term.false)

/-- Native callback policy is shared and survives atomic updates and message delivery. -/
theorem finalizer_policy_every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 24
      (.start {nativeFinalizerMode := .deferred} sharedFinalizerPolicy elapsed) = true := by cbv

private def localAndNative : Result :=
  .nativeSet {nativeRefCounter := 13} <|
    Result.schedule {} (.get fun localEnv => .send [] (.integer localEnv.nativeRefCounter) (.ok .nil)) fun _ =>
      .receive .infinity (fun _ message => some message) fun message =>
        .nativeGet fun nativeEnv => .ok (.tuple #[message.getD .nil, .integer nativeEnv.nativeRefCounter])

/-- Ordinary environment reads remain process-local while native effects share state. -/
theorem localAndNative_every_schedule :
    concurrent localAndNative (.ok (.tuple #[.integer 0, .integer 13])) := by
  refine concurrent_of_check localAndNative
    (fun | .ok (.tuple ⟨[.integer 0, .integer 13]⟩) => true | _ => false) 20 (by intro elapsed; cbv) ?_
  intro result accepted
  split at accepted
  · rfl
  · contradiction

/-- Allocating an Erlang reference leaves the native allocator unchanged. -/
theorem reference_preserves_native_counter (env : Environment) :
    ((Erlang.erlang.«make_ref/0» (Dispatcher.ofTable [] 0)) env).2.nativeRefCounter =
      env.nativeRefCounter := by
  rw [Erlang.erlang.make_ref_apply]

/-- A native identity cannot alias the root's first ordinary reference. -/
theorem native_reference_is_separate (id : Nat) :
    Term.nativeReference id ≠ .reference [1] := by
  simp [Term.nativeReference]

private def traceAcquire (env : Environment) : Option (Unit × Environment) :=
  some ((), {env with nativeRefCounter := 1})

private def traceRelease (env : Environment) : Option (Unit × Environment) :=
  some ((), {env with nativeRefCounter := 2})

private def traceChildAcquire (env : Environment) : Option (Unit × Environment) :=
  if env.nativeRefCounter = 2 then some ((), env) else none

private def traceRegister (env : Environment) : Unit × Environment :=
  ((), {env with nativeResourceTypes := env.nativeResourceTypes ++ ["journal"]})

private def traceParentNext (_ : Unit) : Result := .wait traceRelease (fun _ => .ok .true)
private def traceChildStart (_ : Unit) : Result := .wait traceChildAcquire (fun _ => .ok .true)

/-- Registration is atomic, the child really blocks while the parent holds the
lock, and both suffixes retain the registered capability. -/
theorem atomic_registration_contended_trace :
    (Result.schedule {} (.nativeModify traceRegister traceChildStart)
      (fun _ => .wait traceAcquire traceParentNext)).run {} [.current, .swap [1]] =
      (.ok Term.true, {nativeRefCounter := 2, nativeResourceTypes := ["journal"]}) := by
  have childPrefix : Result.RegisteredPrefix [1] (.nativeModify traceRegister traceChildStart)
      (1, []) [] (.wait traceChildAcquire (fun _ => .ok Term.true)) (1, []) ["journal"] := by
    refine .modify _ _ () _ _ _ _ _ _ _ ?_ (.refl _ _ _)
    intro env pid counter heap types
    cases env
    simp_all [traceRegister]
  have release : Result.SharedSteps [] (traceParentNext ()) (1, []) Term.true (2, []) := by
    refine .wait _ _ () _ _ _ _ ?_ (.done _ _)
    intro env pid counter heap
    cases env
    simp_all [traceRelease]
  simpa [traceParentNext, traceChildStart] using
    (Result.two_registered_modify_interleave_steps
      (.wait traceAcquire traceParentNext) traceRegister traceChildStart
      traceAcquire traceParentNext traceChildAcquire (fun _ => .ok Term.true)
      () () Term.true Term.true
      (0, []) (0, []) (1, []) (1, []) (2, []) (2, []) (2, [])
      [] [] ["journal"] (.refl _ _ _) childPrefix
      (by rfl) release (by simp [traceChildAcquire]) (by simp [traceChildAcquire]) (.done _ _))

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.NativeState

end LynxTest.NativeState
