module

import Lynx
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

end LynxTest.NativeInvariant

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Concurrent
  LynxTest.ProofAudit.checkModule `LynxTest.NativeInvariant
