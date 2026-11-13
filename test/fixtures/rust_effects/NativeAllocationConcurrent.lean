module
public import Allocation.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Allocation.Properties

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-- Execute the actual cross-crate factory, then observe its returned cell.
The observation checks the implementation's arithmetic and stored payload. -/
@[expose] def worker (factory : U64 → U64 → NativeM (Bool × NativeMutex effects_core.Counter))
    (value amount expected : U64) : Result Term := do
  let (changed, mutex) ← factory value amount
  let contents ← NativeM.readCell (NativeMutex.typeName effects_core.Counter) mutex.id
  match contents with
  | .tuple ⟨[.atom "unlocked", .atom "unpoisoned", payload]⟩ =>
    match NativeCodec.decode (α := effects_core.Counter) payload with
    | some counter =>
      if changed && counter.value.val == expected.val then .ok (.integer mutex.id)
      else .ok Term.false
    | none => .ok Term.false
  | _ => .ok Term.false

@[expose] def concurrentFactories
    (factory : U64 → U64 → NativeM (Bool × NativeMutex effects_core.Counter)) : Result Term :=
  Result.schedule {} (do
    let identity ← worker factory 11#u64 5#u64 16#u64
    Result.send [] identity (.ok .nil)) fun _ => do
      let identity ← worker factory 7#u64 3#u64 10#u64
      Result.receive .infinity (fun _ message => some message) fun message =>
        match identity, message with
        | .integer first, some (.integer second) =>
          .ok (if first != second then Term.true else Term.false)
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

/-- Every scheduler transition order retains both initialized payloads and
allocates distinct identities. The depth is a checked exploration bound, not
a bound on the number or contents of supplied scheduler choices. -/
theorem every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 24
      (.start {} (concurrentFactories mutex_new_incremented) elapsed) = true := by
  have first := checked_sum 7#u64 3#u64 10#u64 (by decide +kernel)
  have second := checked_sum 11#u64 5#u64 16#u64 (by decide +kernel)
  simp only [concurrentFactories, worker, mutex_new_incremented, effects_core.increment,
    first, second, NativeM.ok, monadLift_self]
  cbv

/-- Every actual run preserves both initialized cells and their distinct identities. -/
theorem every_run :
    concurrent (concurrentFactories mutex_new_incremented) (.ok Term.true) := by
  intro elapsed events last outcome run terminal
  have checked := Concurrent.check_sound (every_interleaving elapsed) run terminal
  split at checked
  · rfl
  · contradiction

end Allocation.Properties
