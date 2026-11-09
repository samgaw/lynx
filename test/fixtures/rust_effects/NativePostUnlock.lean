module
public import Tail.Critical
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Tail.PostUnlock
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 2000000

/-- Compose the existing implementation contract, keeping resource destruction
strictly after the actual guard-release operation. -/
theorem composed_contract (mutex : NativeMutex effects_core.Counter)
    (resource : NativeResourceArc ScalarResource) :
    locked_increment_then_release_resource mutex resource = (do
      let data ← NativeResourceArc.deref resource
      let acquired ← NativeMutex.lock mutex
      let guard ← effects_core.recover_guard acquired
      let (changed, updated) ← effects_core.increment guard.value data.counter.value
      NativeGuard.release {guard with value := updated}
      NativeOwnedDrop.drop resource
      NativeM.ok changed) := by
  simp only [locked_increment_then_release_resource, scalar_resource_read,
    effects_core.counter_value, Tail.Critical.critical_contract, NativeM.ok,
    monadLift_self, bind_assoc, Result.ok_bind]

@[expose] def payload (amount : U64) : ScalarResource := ⟨⟨amount⟩⟩
@[expose] def free (value : U64) : Term :=
  .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk value)]
@[expose] def pin (amount : U64) := NativeResourceArc.vmCells (payload amount) 2 4 5
@[expose] def finalHeap (amount total : U64) :=
  pin amount ++ [(1, NativeMutex.typeName effects_core.Counter, free total), (3, "unrelated", .integer 17)]

@[expose] def initial (before amount : U64) : Environment :=
  {nativeRefCounter := 7, nativeResourceTypes := [NativeResourceArc.typeName ScalarResource],
    nativeHeap :=
      (7, NativeResourceArc.handleType ScalarResource, .nativeReference 2) ::
      (6, NativeResourceArc.handleType ScalarResource, .nativeReference 2) ::
      ((pin amount).map fun cell => if cell.1 == 2 then
        (2, NativeResourceArc.typeName ScalarResource, .tuple #[.integer 3, NativeCodec.encode (payload amount)]) else cell) ++
      [(1, NativeMutex.typeName effects_core.Counter, free before), (3, "unrelated", .integer 17)]}

@[expose] def inspect (amount total : U64) : Result Term :=
  .nativeGet fun env => .ok (if env.nativeRefCounter == 9 && env.nativeHeap == finalHeap amount total
    then Term.true else Term.false)

@[expose] def parallel
    (worker : NativeMutex effects_core.Counter → NativeResourceArc ScalarResource → NativeM Bool)
    (amount total : U64) (successes : Nat) : Result Term :=
  Result.schedule {} (do
    let changed ← worker ⟨1⟩ ⟨2,6⟩
    Result.send [] (if changed then Term.true else Term.false) (.ok .nil)) fun _ => do
      let changed ← worker ⟨1⟩ ⟨2,7⟩
      Result.receive .infinity (fun _ message => some message) fun message =>
        match message with
        | some (.atom "true") => if (if changed then 1 else 0) + 1 == successes then
            inspect amount total else .ok Term.false
        | some (.atom "false") => if (if changed then 1 else 0) == successes then
            inspect amount total else .ok Term.false
        | _ => .ok Term.false

/-- Both complete real Rust calls, including the unlocked owner-release suffix,
retain the VM pin and unrelated cell and commit both counter updates. -/
theorem all_interleavings :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 96
      (.start (initial 7#u64 3#u64)
        (parallel locked_increment_then_release_resource 3#u64 13#u64 2)) = true := by
  simp only [parallel, composed_contract]
  cbv

/-- Checked failure also releases its owner after unlocking. Exactly one update
fits, and neither attempted call poisons the mutex or loses the VM pin. -/
theorem overflow_interleavings :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 96
      (.start (initial 18446744073709551614#u64 1#u64)
        (parallel locked_increment_then_release_resource 1#u64 18446744073709551615#u64 1)) = true := by
  simp only [parallel, composed_contract]
  cbv

theorem all_choices (choices : List ScheduleChoice) :
    concurrentFrom (initial 7#u64 3#u64)
      (parallel locked_increment_then_release_resource 3#u64 13#u64 2) choices = .ok Term.true := by
  obtain ⟨_, _, run, final⟩ := Result.run_reaches
    (parallel locked_increment_then_release_resource 3#u64 13#u64 2) (initial 7#u64 3#u64) choices
  have checked := Concurrent.check_sound all_interleavings run final
  rw [← concurrentFrom_eq_run] at checked
  split at checked
  · assumption
  · contradiction

theorem overflow_choices (choices : List ScheduleChoice) :
    concurrentFrom (initial 18446744073709551614#u64 1#u64)
      (parallel locked_increment_then_release_resource 1#u64 18446744073709551615#u64 1) choices = .ok Term.true := by
  obtain ⟨_, _, run, final⟩ := Result.run_reaches
    (parallel locked_increment_then_release_resource 1#u64 18446744073709551615#u64 1)
    (initial 18446744073709551614#u64 1#u64) choices
  have checked := Concurrent.check_sound overflow_interleavings run final
  rw [← concurrentFrom_eq_run] at checked
  split at checked
  · assumption
  · contradiction
end Tail.PostUnlock
