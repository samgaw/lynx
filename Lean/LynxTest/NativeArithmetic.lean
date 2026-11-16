module

import Lynx
import Lynx.Runner.NativeArithmetic
meta import LynxTest.ProofAudit

namespace LynxTest.NativeArithmetic
open Lynx

section
open scoped Lynx.NativeArithmetic

theorem counter_bounds (counter : Nat) (positive : 1 ≤ counter) :
    (Nat.ble 1 counter && Nat.ble counter (counter + 4) &&
      !(Nat.beq 0 counter) && !(Nat.beq (counter + 1) (counter + 2))) = true := by cbv

private def allocateTwo : Result Nat :=
  .nativeModify (fun env => (env.nativeRefCounter + 1,
    {env with nativeRefCounter := env.nativeRefCounter + 1})) fun first =>
  .nativeModify (fun env => (env.nativeRefCounter + 1,
    {env with nativeRefCounter := env.nativeRefCounter + 1})) fun second =>
  if first == second then .error .exhausted else .ok second

theorem intermediate_bounds (counter : Nat) :
    Result.NativeInvariant.check (fun env =>
      counter ≤ env.nativeRefCounter && env.nativeRefCounter ≤ counter + 2)
      4 allocateTwo {nativeRefCounter := counter} = true := by cbv

example (_counter : Nat) : True := by
  fail_if_success have : Nat.beq _counter 0 = true := by cbv
  fail_if_success have : Nat.ble (_counter + 1) _counter = true := by cbv
  trivial

end

-- Importing the helper does not enable arithmetic rewriting in other proofs.
example (_counter : Nat) : True := by
  fail_if_success have : Nat.ble _counter (_counter + 4) = true := by cbv
  trivial

end LynxTest.NativeArithmetic

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Runner.NativeArithmetic
  LynxTest.ProofAudit.checkModule `LynxTest.NativeArithmetic
