module
public import Cleanup.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Cleanup.Properties

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local cbv_eval] Term.compare_atoms

/-- One worker completes actual compiler-generated destruction while another
retains and subsequently reads its own independently constructed mutex. -/
@[expose] def concurrentCleanup
    (factory : U64 → U64 → NativeM (Bool × NativeMutex effects_core.Counter))
    (cleanup : U64 → NativeM Bool) : Result Term :=
  Result.schedule {} (do
    let completed ← cleanup 11#u64
    Result.send [] (if completed then .atom "done" else .atom "failed") (.ok .nil)) fun _ => do
      let (changed, mutex) ← factory 7#u64 3#u64
      Result.receive .infinity (fun _ message => some message) fun message => do
        let contents ← NativeM.readCell (NativeMutex.typeName effects_core.Counter) mutex.id
        .nativeGet fun env =>
          match message, contents with
          | some (.atom "done"), .tuple ⟨[.atom "unlocked", .atom "unpoisoned", payload]⟩ =>
            match NativeCodec.decode (α := effects_core.Counter) payload with
            | some counter =>
              .ok (if changed && counter.value.val == 10 && env.nativeRefCounter == 2 &&
                env.nativeHeap.length == 1 then Term.true else Term.false)
            | none => .ok Term.false
          | _, _ => .ok Term.false

private theorem checked_sum (value amount total : U64)
    (sum : total.val = value.val + amount.val) :
    U64.checked_add value amount = some total := by
  have specification := U64.checked_add_bv_spec value amount
  cases result : U64.checked_add value amount with
  | none =>
      simp only [result] at specification
      have bounded : total.val ≤ U64.max := by scalar_tac
      omega
  | some returned =>
      simp only [result] at specification
      have same : returned = total := by scalar_tac
      simp only [same]

/-- Destruction consumes the child's cell, preserves the parent's payload and
never rewinds the shared identity supply under any transition order. -/
theorem every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 32
      (.start {} (concurrentCleanup mutex_new_incremented mutex_scope_flag) elapsed) = true := by
  have sum := checked_sum 7#u64 3#u64 10#u64 (by decide +kernel)
  simp only [concurrentCleanup, mutex_new_incremented, effects_core.increment,
    sum, NativeM.ok, monadLift_self]
  cbv

theorem every_run :
    concurrent (concurrentCleanup mutex_new_incremented mutex_scope_flag) (.ok Term.true) := by
  intro elapsed events last outcome run terminal
  have checked := Concurrent.check_sound (every_interleaving elapsed) run terminal
  split at checked
  · rfl
  · contradiction

end Cleanup.Properties
