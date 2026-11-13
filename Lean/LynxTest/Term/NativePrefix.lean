module

import Lynx.Term.NativeTrace.Prefix
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativePrefix

open Lynx

private def waitForPeer : Result Term :=
  .wait (fun env => if env.nativeRefCounter % 2 = 0 then some ((), env) else none) fun _ =>
    .nativeGet fun env => .ok (.integer env.nativeRefCounter)

private def registerAndDecode : Result Term :=
  .nativeModify (fun env => ((), {env with
    nativeRefCounter := env.nativeRefCounter + 1,
    nativeResourceTypes := env.nativeResourceTypes ++ ["counter"]})) fun _ =>
      .nativeGet fun env =>
        if 0 < env.nativeRefCounter then waitForPeer else .error .exhausted

private theorem actual_prefix (counter : Nat) (heap : List (Nat × String × Term)) (types : List String) :
    Result.RegisteredPrefix [] registerAndDecode (counter, heap) types waitForPeer
      (counter + 1, heap) (types ++ ["counter"]) := by
  refine .modify _ _ () _ (counter + 1, heap) _ _ (types ++ ["counter"]) _ _ ?_ ?_
  · intro env _ count stored registered
    simp [count, stored, registered]
  · refine .read _ waitForPeer _ _ _ _ _ ?_ (.refl _ _ _)
    intro env _ count _ _
    simp [count]

/-- Both actual prefix callbacks run before the first native wait. Normalizing
them retains an arbitrary child and every remaining scheduler choice. -/
theorem normalization_keeps_choices (counter : Nat) (heap : List (Nat × String × Term))
    (types : List String) (child : Result Term) (choices : List ScheduleChoice) :
    (Result.schedule {} child (fun _ => registerAndDecode)).run
      {nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types} (.current :: choices) =
    (Result.schedule {} child (fun _ => waitForPeer)).run
      {nativeRefCounter := counter + 1, nativeHeap := heap,
        nativeResourceTypes := types ++ ["counter"]} (.current :: choices) :=
  (actual_prefix counter heap types).spawnCurrent child choices

end LynxTest.Term.NativePrefix

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Prefix
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativePrefix
