module

import Lynx
import Lynx.Runner.CheckPost
meta import LynxTest.ProofAudit

namespace LynxTest.CheckPost
open Lynx Concurrent

private def increment : Result Unit :=
  .nativeModify (fun env => ((), {env with nativeRefCounter := env.nativeRefCounter + 1})) .ok

private def program : Result := Result.schedule {} (do increment; .ok .nil) fun _ => do
  increment
  .ok .true

private def counter (expected : Nat) (config : Config Term) : Bool :=
  match config with
  | .running state .. => config.outcome.isTrue && state.nativeRefCounter == expected
  | _ => false

set_option maxRecDepth 8192
set_option maxHeartbeats 16000000

/-- The parent may finish first. Every terminal run must include both native writes. -/
theorem native_counter (elapsed : PID → Nat → Nat) :
    checkPost (counter 2) 20 (.start {} program elapsed) = true := by lynx_check_post

theorem every_native_run (elapsed : PID → Nat → Nat)
    (run : Run (.start {} program elapsed) events last) (terminal : Terminal last outcome) :
    counter 2 last = true := checkPost_sound (native_counter elapsed) run terminal

/-- error: postcondition rejected at a terminal configuration -/
#guard_msgs in
example (elapsed : PID → Nat → Nat) :
    checkPost (fun _ : Config Term => false) 20 (.start {} program elapsed) = true := by
  lynx_check_post

private def racing : Result := Result.schedule {}
  (.nativeModify (fun env => ((), {env with nativeRefCounter := 1})) fun _ => .ok .nil) fun _ =>
    .nativeModify (fun env => ((), {env with nativeRefCounter := 2})) fun _ => .ok .true

-- Identical successful outcomes cannot justify reusing different native states.
/-- error: postcondition rejected at a terminal configuration -/
#guard_msgs in
example (elapsed : PID → Nat → Nat) :
    checkPost (counter 1) 20 (.start {} racing elapsed) = true := by lynx_check_post

/-- error: postcondition search exhausted its step bound -/
#guard_msgs in
example (elapsed : PID → Nat → Nat) :
    checkPost (fun _ : Config Term => true) 0 (.start {} program elapsed) = true := by
  lynx_check_post

/-- error: postcondition search exhausted its step bound -/
#guard_msgs in
example (elapsed : PID → Nat → Nat) :
    checkPost (counter 2) 1 (.start {} program elapsed) = true := by lynx_check_post

private def raised : Result := .error (.error (.atom "failed"))

private def expectedError (config : Config Term) : Bool :=
  match config.outcome with
  | .error (.error (.atom "failed")) => true
  | _ => false

theorem error_preserved (elapsed : PID → Nat → Nat) :
    checkPost expectedError 4 (.start {} raised elapsed) = true := by lynx_check_post

/-- error: postcondition rejected at a terminal configuration -/
#guard_msgs in
example (elapsed : PID → Nat → Nat) :
    checkPost (fun config => config.outcome.isTrue) 4 (.start {} raised elapsed) = true := by
  lynx_check_post

end LynxTest.CheckPost

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Runner.CheckPost
  LynxTest.ProofAudit.checkModule `LynxTest.CheckPost
