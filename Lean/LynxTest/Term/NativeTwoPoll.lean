module

import Lynx.Term.NativeTrace.Contended
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeTwoPoll

open Lynx

private def acquire (env : Environment) : Option (Nat × Environment) :=
  if env.nativeHeap.isEmpty then
    some (env.nativeRefCounter, {env with nativeHeap := [(1, "owner", .pid env.currentPid)]})
  else none

private def release (value : Nat) (env : Environment) : Option (Nat × Environment) :=
  if env.pdict.isEmpty && env.refCounter == 0 then
    match env.nativeHeap with
    | [(1, "owner", .pid owner)] =>
        if owner == env.currentPid then
          some (value + 1, {env with nativeRefCounter := value + 1, nativeHeap := []}) else none
    | _ => none
  else none

private def finish (value : Nat) : Result Term := .ok (.integer value)
private def critical (value : Nat) : Result Term := .wait (release value) finish

/-- The wrapper needs callback equations at the actual fresh process states.
These callbacks intentionally reject other process-local environments. -/
theorem exact_state_parent_first (counter : Nat) :
    (Result.schedule {} (.wait acquire critical) (fun _ => .wait acquire critical)).run
      {nativeRefCounter := counter} [.current, .swap [1]] =
      (.ok (.integer (counter + 1)), {nativeRefCounter := counter + 2}) := by
  exact Result.two_wait_interleave acquire critical acquire critical
    (release counter) finish (release (counter + 1)) finish
    counter (counter + 1) (counter + 1) (counter + 2)
    (.integer (counter + 1)) (.integer (counter + 2))
    (counter, []) (counter, [(1, "owner", .pid [])]) (counter + 1, [])
    (counter + 1, [(1, "owner", .pid [1])]) (counter + 2, [])
    (by simp [acquire]) rfl (by simp [acquire]) (by simp [release]) rfl
    (by simp [acquire]) rfl (by simp [release]) rfl

/-- The child-first schedule preserves the root's later acquired value, and
the actual release callbacks still see their exact process-local states. -/
theorem exact_state_child_first (counter : Nat) :
    (Result.schedule {} (.wait acquire critical) (fun _ => .wait acquire critical)).run
      {nativeRefCounter := counter} [.swap [1], .swap []] =
      (.ok (.integer (counter + 2)), {nativeRefCounter := counter + 2}) := by
  exact Result.two_wait_interleave_child_first acquire critical acquire critical
    (release (counter + 1)) finish (release counter) finish
    (counter + 1) counter (counter + 2) (counter + 1)
    (.integer (counter + 2)) (.integer (counter + 1))
    (counter, []) (counter, [(1, "owner", .pid [1])]) (counter + 1, [])
    (counter + 1, [(1, "owner", .pid [])]) (counter + 2, [])
    (by simp [acquire]) rfl (by simp [acquire]) (by simp [release]) rfl
    (by simp [acquire]) rfl (by simp [release]) rfl

/-- These concrete observations differ, so a fixed-outcome law cannot silently
replace the actual schedules by a single favorable execution. -/
theorem schedules_have_different_root_results (counter : Nat) :
    ((Result.schedule {} (.wait acquire critical) (fun _ => .wait acquire critical)).run
      {nativeRefCounter := counter} [.current, .swap [1]]).1 ≠
    ((Result.schedule {} (.wait acquire critical) (fun _ => .wait acquire critical)).run
      {nativeRefCounter := counter} [.swap [1], .swap []]).1 := by
  rw [exact_state_parent_first, exact_state_child_first]
  simp

/-- A contract over every environment would be stronger than the wrapper's
original contract and would reject this actual callback. -/
theorem noncanonical_release_rejected (counter : Nat) :
    release counter {pdict := [(.nil, .nil)], nativeHeap := [(1, "owner", .pid [])]} = none := by
  rfl

end LynxTest.Term.NativeTwoPoll

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeTwoPoll
