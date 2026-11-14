module

import Lynx
import Lynx.Rustler
meta import LynxTest.ProofAudit

namespace LynxTest.NativeInvariant
open Lynx Concurrent

private def nativeCounter : Config Term → Nat
  | .start env .. => env.nativeRefCounter
  | .running state .. => state.nativeRefCounter

private def transient : Result :=
  .nativeModify (fun env => ((), {env with nativeRefCounter := 7})) fun _ =>
    .nativeModify (fun env => ((), {env with nativeRefCounter := 0})) fun _ => .ok .true

private def unchanged (config : Config Term) : Bool := nativeCounter config == 0

-- A terminal-only check misses a temporary violation restored before returning.
theorem transient_terminal (elapsed : PID → Nat → Nat) :
    checkPost unchanged 8 (.start {} transient elapsed) = true := by cbv

theorem transient_rejected (elapsed : PID → Nat → Nat) :
    checkInvariant unchanged 8 (.start {} transient elapsed) = false := by cbv

private def increment : Result Unit :=
  .nativeModify (fun env => ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) .ok

private def joined : Result := Result.schedule {} (do increment; .ok .nil) fun _ => do
  increment
  .ok .true

private def bounded (config : Config Term) : Bool := decide (nativeCounter config ≤ 2)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 16000000 in
theorem every_prefix_checked (elapsed : PID → Nat → Nat) :
    checkInvariant bounded 20 (.start {} joined elapsed) = true := by cbv

theorem every_prefix_safe (elapsed : PID → Nat → Nat)
    (run : Run (.start {} joined elapsed) events last) : bounded last = true :=
  checkInvariant_sound (every_prefix_checked elapsed) run

theorem exhausted (config : Config Term) :
    checkInvariant (fun _ => true) 0 config = false := rfl

private def pending : Result := .wait (fun _ => none) fun _ : Unit => .ok .true

-- Invariant safety while blocked does not establish successful completion.
theorem pending_safe (elapsed : PID → Nat → Nat) :
    checkInvariant unchanged 4 (.start {} pending elapsed) = true := by cbv

theorem pending_not_success (elapsed : PID → Nat → Nat) :
    check Outcome.isTrue 4 (.start {} pending elapsed) = false := by cbv

private def once (env : Environment) : Prop := env.nativeRefCounter ≤ 1

private def failing (exception : Exception) : Result Bool :=
  .nativeModify (fun env => ((),{env with nativeRefCounter := 1})) fun _ => .error exception

theorem failing_safe (exception : Exception) : Result.NativeInvariant once (failing exception) {} := by
  unfold failing
  apply Result.NativeInvariant.nativeModify _ _ _ (by simp [once])
  exact .error _ _ _ (by simp [once])

theorem panic_conversion_safe : Result.NativeInvariant once
    (Rustler.executeNative (failing (.error (.atom "rust_panicked"))) Rustler.encodeBool) {} :=
  Rustler.executeNative_invariant (failing_safe _) _

private def panicRetained (config : Config Term) : Bool :=
  match config.outcome with
  | .error (.error (.atom "nif_panicked")) => nativeCounter config == 1
  | _ => false

theorem panic_retains_mutation : checkPost panicRetained 8
    (.start {} (Rustler.executeNative (failing (.error (.atom "rust_panicked"))) Rustler.encodeBool)) = true := by
  cbv

private def exhaustedRetained (config : Config Term) : Bool :=
  match config.outcome with
  | .error .exhausted => nativeCounter config == 1
  | _ => false

theorem exhaustion_not_caught : checkPost exhaustedRetained 8
    (.start {} (Rustler.executeNative (failing .exhausted) Rustler.encodeBool)) = true := by
  cbv

private def blockedAfterMutation : Result Bool :=
  .nativeModify (fun env => ((),{env with nativeRefCounter := 1})) fun _ =>
    .wait (fun _ => none) fun _ : Unit => .ok true

private def blockedRetained (config : Config Term) : Bool :=
  match config.outcome with
  | .deadlock => nativeCounter config == 1
  | _ => false

theorem blocking_not_caught : checkPost blockedRetained 8
    (.start {} (Rustler.executeNative blockedAfterMutation Rustler.encodeBool)) = true := by
  cbv

private def successful : Result Bool :=
  .nativeModify (fun env => ((),{env with nativeRefCounter := env.nativeRefCounter + 1})) fun _ =>
    .wait (fun env => some ((),{env with nativeRefCounter := env.nativeRefCounter + 2})) fun _ : Unit => .ok true

/-- The inverse adapter rule returns the actual computation prefix, including
both native state changes. The premise is witnessed by the real forward rule. -/
theorem encoded_success_has_origin :
    ∃ value, Term.true = Rustler.encodeBool value ∧
      Result.ReadyPrefix successful {} (.ok value) {nativeRefCounter := 3} := by
  have native : Result.ReadyPrefix successful {} (.ok true) {nativeRefCounter := 3} := by
    unfold successful
    exact .nativeModify _ _ () _ _ _ _ rfl (.wait _ _ () _ _ _ _ rfl (.refl _ _))
  exact Rustler.executeNative_returns (Rustler.executeNative_readyPrefix native Rustler.encodeBool)

private theorem failing_no_return (exception : Exception) (encoded : Term) (world : Environment)
    (trace : Result.ReadyPrefix (Rustler.executeNative (failing exception) Rustler.encodeBool)
      {} (.ok encoded) world) : False := by
  obtain ⟨value,_,original⟩ := Rustler.executeNative_returns trace
  unfold failing at original
  cases original with
  | nativeModify _ _ _ _ _ _ _ _ rest => cases rest

/-- Neither panic conversion nor verification exhaustion can fabricate a
successful encoded result after the native mutation. -/
theorem panic_cannot_return (encoded : Term) (world : Environment)
    (trace : Result.ReadyPrefix (Rustler.executeNative (failing (.error (.atom "rust_panicked"))) Rustler.encodeBool)
      {} (.ok encoded) world) : False := failing_no_return _ encoded world trace

theorem exhaustion_cannot_return (encoded : Term) (world : Environment)
    (trace : Result.ReadyPrefix (Rustler.executeNative (failing .exhausted) Rustler.encodeBool)
      {} (.ok encoded) world) : False := failing_no_return _ encoded world trace

end LynxTest.NativeInvariant

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeInvariant
  LynxTest.ProofAudit.checkModule `Lynx.Rustler
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent
  LynxTest.ProofAudit.checkModule `LynxTest.NativeInvariant
