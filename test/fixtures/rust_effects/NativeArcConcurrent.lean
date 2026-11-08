module
public import Retain.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Retain.Properties
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local cbv_eval] Term.compare_atoms Term.compare_reference

@[expose] def twoClones
    (clone : NativeResourceArc ScalarResource → NativeM (NativeResourceArc ScalarResource))
    (read : NativeResourceArc ScalarResource → NativeM U64) : Result Term :=
  Result.schedule {} (do
    let retained ← clone ⟨1,2⟩
    let observed ← read retained
    Result.send [] (.tuple #[.integer retained.token, .integer observed.val]) (.ok .nil)) fun _ => do
      let retained ← clone ⟨1,3⟩
      let observed ← read retained
      Result.receive .infinity (fun _ message => some message) fun message =>
        .nativeGet fun env =>
          match message, env.nativeHeap.filter (fun cell => cell.1 == 1) with
          | some (.tuple ⟨[.integer peer, .integer seen]⟩),
              [(1,_,.tuple ⟨[.integer count,payload]⟩)] =>
            match NativeCodec.decode (α := ScalarResource) payload with
            | some resource => .ok (
                if observed.val == 42 && seen == 42 && resource.counter.value.val == 42 &&
                  count == 4 && peer != retained.token && retained.id == 1 &&
                  env.nativeRefCounter == 5 && env.nativeHeap.length == 5
                then Term.true else Term.false)
            | none => .ok Term.false
          | _, _ => .ok Term.false

@[expose] def initial : Environment :=
  {nativeResourceTypes := [NativeResourceArc.typeName ScalarResource], nativeRefCounter := 3, nativeHeap := [
    (3,NativeResourceArc.handleType ScalarResource,.nativeReference 1),
    (2,NativeResourceArc.handleType ScalarResource,.nativeReference 1),
    (1,NativeResourceArc.typeName ScalarResource,
      .tuple #[.integer 2,NativeCodec.encode ({counter := {value := 42#u64}} : ScalarResource)])]}

/-- Independent owners retain one allocation without losing a token or payload. -/
theorem every_interleaving :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 32
      (.start initial (twoClones scalar_resource_clone scalar_resource_read)) = true := by cbv

theorem every_schedule (choices : List ScheduleChoice) :
    concurrentFrom initial (twoClones scalar_resource_clone scalar_resource_read) choices = .ok Term.true := by
  obtain ⟨_,_,run,final⟩ := Result.run_reaches
    (twoClones scalar_resource_clone scalar_resource_read) initial choices
  have checked := Concurrent.check_sound every_interleaving run final
  rw [← concurrentFrom_eq_run] at checked
  split at checked
  · assumption
  · contradiction
end Retain.Properties
