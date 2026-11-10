module
public import RwShared.Properties
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace RwShared.Contention

/-- Repeated native type tags need no byte-by-byte equality certificate. -/
@[cbv_eval] theorem sameString (value : String) : (value == value) = true := by simp

/-- Two actual Rust critical sections share one resource. The parent waits for
child completion before the final actual Rust read consumes the last owner.
Registration availability is an explicit loader-model capability. -/
@[expose] def competing
    (factory : Bool → NativeM (core.result.Result (NativeResourceArc RwResource) Unit))
    (retain : NativeResourceArc RwResource → NativeM (NativeResourceArc RwResource))
    (update read : NativeResourceArc RwResource → NativeM Bool)
    (value : Bool) : Result Term :=
  Rustler.withResourceTypes [NativeResourceArc.typeName RwResource] do
    let owner ← NativeM.resumeCaptured (factory value)
    let child ← retain owner
    let writer ← retain owner
    Result.schedule {} (do
      let _ ← update child
      Result.send [] (.atom "done") (.ok .nil)) fun _ => do
        let _ ← update writer
        let _ ← Result.receive .infinity (fun _ message => some message) .ok
        let result ← read owner
        .nativeGet fun env => .ok (if result == value && env.nativeHeap.isEmpty then Term.true else Term.false)

set_option maxRecDepth 4096
set_option maxHeartbeats 8000000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Term.compare_atoms

/-- Exhaustively explore the finite logical interleavings of actual extracted
Rust bodies. This is not a claim about OS fairness or VM thread correspondence. -/
theorem every_interleaving (value : Bool) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 80
      (.start {} (competing rw_resource_new rw_resource_clone rw_resource_update rw_resource_read value)) = true := by
  cases value <;> cbv

theorem every_schedule (value : Bool) (choices : List ScheduleChoice) :
    concurrent (competing rw_resource_new rw_resource_clone rw_resource_update rw_resource_read value) choices = .ok Term.true := by
  have checked := concurrent_of_check (competing rw_resource_new rw_resource_clone rw_resource_update rw_resource_read value)
    (fun | .ok (.atom "true") => true | _ => false) 80 (every_interleaving value) choices
  split at checked
  · assumption
  · contradiction

end RwShared.Contention
