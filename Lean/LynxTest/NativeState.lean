module

import Lynx
import Lynx.Modules.Erlang.erlang
meta import LynxTest.ProofAudit

namespace LynxTest.NativeState
open Lynx

private def sharedUpdate : Result :=
  Result.schedule {} (.nativeSet {nativeRefCounter := 7} (.ok .nil)) fun _ =>
    .wait (fun env => if env.nativeRefCounter = 7 then some ((), env) else none) fun _ =>
      .nativeGet fun env => .ok (.integer env.nativeRefCounter)

/-- A native write made by a child is visible to the parent under every schedule. -/
theorem sharedUpdate_every_schedule (choices : List ScheduleChoice) :
    concurrent sharedUpdate choices = .ok (.integer 7) := by
  have checked := concurrent_of_check sharedUpdate
    (fun | .ok (.integer 7) => true | _ => false) 16 (by cbv) choices
  split at checked
  · assumption
  · contradiction

private def localAndNative : Result :=
  .nativeSet {nativeRefCounter := 13} <|
    Result.schedule {} (.get fun localEnv => .send [] (.integer localEnv.nativeRefCounter) (.ok .nil)) fun _ =>
      .receive .infinity (fun _ message => some message) fun message =>
        .nativeGet fun nativeEnv => .ok (.tuple #[message.getD .nil, .integer nativeEnv.nativeRefCounter])

/-- Ordinary environment reads remain process-local while native effects share state. -/
theorem localAndNative_every_schedule (choices : List ScheduleChoice) :
    concurrent localAndNative choices = .ok (.tuple #[.integer 0, .integer 13]) := by
  have checked := concurrent_of_check localAndNative
    (fun | .ok (.tuple ⟨[.integer 0, .integer 13]⟩) => true | _ => false) 20 (by cbv) choices
  split at checked
  · assumption
  · contradiction

/-- Allocating an Erlang reference leaves the native allocator unchanged. -/
theorem reference_preserves_native_counter (env : Environment) :
    ((Erlang.erlang.«make_ref/0» (Dispatcher.ofTable #[] 0)) env).2.nativeRefCounter =
      env.nativeRefCounter := by
  rw [Erlang.erlang.make_ref_apply]

/-- A native identity cannot alias the root's first ordinary reference. -/
theorem native_reference_is_separate (id : Nat) :
    Term.nativeReference id ≠ .reference [1] := by
  simp [Term.nativeReference]

run_cmd do
  LynxTest.ProofAudit.checkModule `LynxTest.NativeState

end LynxTest.NativeState
