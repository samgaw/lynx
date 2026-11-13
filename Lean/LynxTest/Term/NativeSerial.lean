module

import Lynx.Term.NativeTrace.Serial
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeSerial

open Lynx

private def increment : Result Term :=
  .nativeModify (fun env =>
    (env.nativeRefCounter + 1, {env with nativeRefCounter := env.nativeRefCounter + 1})) fun value =>
      .wait (fun env => some ((), env)) fun _ => .ok (.integer value)

private theorem increment_trace (pid : PID) (counter : Nat) (heap : List (Nat × String × Term)) :
    Result.SharedSteps pid increment (counter, heap) (.integer (counter + 1)) (counter + 1, heap) := by
  refine .modify _ _ (counter + 1) _ (counter + 1, heap) _ _ ?_ ?_
  · intro env _ count stored
    simp [count, stored]
  · refine .wait _ _ () _ (counter + 1, heap) _ _ ?_ (.done _ _)
    intro env _ count stored
    cases env
    simp_all

/-- The original serial certificate is usable through ordinary public imports.
Both actual callbacks and both ready waits execute; the child updates the shared
state after the root has computed its own return value. -/
theorem serial_result (counter : Nat) (heap : List (Nat × String × Term)) :
    (Result.schedule {} increment (fun _ => increment)).run
      {nativeRefCounter := counter, nativeHeap := heap} [] =
      (.ok (.integer (counter + 1)), {nativeRefCounter := counter + 2, nativeHeap := heap}) := by
  exact Result.two_shared_serial_steps increment increment
    (.integer (counter + 1)) (.integer (counter + 2))
    (counter, heap) (counter + 1, heap) (counter + 2, heap)
    (increment_trace [] counter heap) (increment_trace [1] (counter + 1) heap)

private def registerAndIncrement : Result Term :=
  .nativeModify (fun env =>
    ((), {env with nativeResourceTypes := env.nativeResourceTypes ++ ["counter"]})) fun _ => increment

private theorem registered_trace (pid : PID) (counter : Nat) (heap : List (Nat × String × Term))
    (types : List String) :
    Result.RegisteredSteps pid registerAndIncrement (counter, heap) types (.integer (counter + 1))
      (counter + 1, heap) (types ++ ["counter"]) := by
  refine .modify _ _ () _ (counter, heap) _ _ (types ++ ["counter"]) _ _ ?_
    (.shared (increment_trace pid counter heap) _)
  intro env _ count stored registered
  simp [count, stored, registered]

/-- Registration effects from both native calls remain in the final state. This
is a synthetic runtime callback; it does not claim compiled Rustler qualification. -/
theorem registered_serial_result (counter : Nat) (heap : List (Nat × String × Term))
    (types : List String) :
    (Result.schedule {} registerAndIncrement (fun _ => registerAndIncrement)).run
      {nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types} [] =
      (.ok (.integer (counter + 1)), {
        nativeRefCounter := counter + 2, nativeHeap := heap,
        nativeResourceTypes := (types ++ ["counter"]) ++ ["counter"]}) := by
  exact Result.two_registered_serial_steps registerAndIncrement registerAndIncrement
    (.integer (counter + 1)) (.integer (counter + 2))
    (counter, heap) (counter + 1, heap) (counter + 2, heap)
    types (types ++ ["counter"]) ((types ++ ["counter"]) ++ ["counter"])
    (registered_trace [] counter heap types)
    (registered_trace [1] (counter + 1) heap (types ++ ["counter"]))

/-- Root completion cannot discard the child's later native write. -/
theorem child_write_not_lost (counter : Nat) (heap : List (Nat × String × Term)) :
    ((Result.schedule {} increment (fun _ => increment)).run
      {nativeRefCounter := counter, nativeHeap := heap} []).2.nativeRefCounter ≠ counter + 1 := by
  rw [serial_result]
  simp

end LynxTest.Term.NativeSerial

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Serial
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeSerial
