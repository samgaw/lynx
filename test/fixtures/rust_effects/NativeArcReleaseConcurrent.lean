module
public import Reclaim.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Reclaim.Properties
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 2000000
attribute [local cbv_eval] Term.compare_atoms Term.compare_reference

@[expose] def inspectHeap : Result Term :=
  .nativeGet fun env =>
    match env.nativeHeap with
    | [(5,"unrelated",.integer payload)] => .ok (
        if payload == 17 && env.nativeRefCounter == 5 then Term.true else Term.false)
    | _ => .ok Term.false

/-- The callback is explicitly dispatched; this does not spawn a VM callback
thread or identify native callback jobs with BEAM process identities. -/
@[expose] def finalizerRace : Result Term :=
  Result.schedule {} (do
    let status ← NativeResourceArc.runFinalizer (α := CounterResource) 2
    Result.send [] (match status with
      | .idle => .atom "idle" | .busy => .atom "busy" | .completed => .atom "completed") (.ok .nil)) fun _ => do
      let status ← NativeResourceArc.runFinalizer (α := CounterResource) 2
      Result.receive .infinity (fun _ message => some message) fun message =>
        match status, message with
        | .completed, some (.atom "idle") | .completed, some (.atom "busy")
        | .idle, some (.atom "completed") | .busy, some (.atom "completed") => inspectHeap
        | _, _ => .ok Term.false

@[expose] def inspectPending : Result Term :=
  .nativeGet fun env =>
    match env.nativeHeap with
    | [(2,tag,payload), (1,_,_), (5,"unrelated",.integer untouched)] =>
      match NativeCodec.decode (α := CounterResource) payload with
      | some resource => .ok (
          if tag == NativeResourceArc.finalizerType CounterResource && resource.state.id == 1 &&
            untouched == 17 && env.nativeRefCounter == 5 then Term.true else Term.false)
      | none => .ok Term.false
    | _ => .ok Term.false

@[expose] def releaseBoth
    (release : NativeResourceArc CounterResource → NativeM Bool) (parentToken : Nat)
    (finish : Result Term) : Result Term :=
  Result.schedule {} (do
    let acknowledged ← release ⟨2,3⟩
    Result.send [] (if acknowledged then .atom "done" else .atom "failed") (.ok .nil)) fun _ => do
      let acknowledged ← release ⟨2,parentToken⟩
      Result.receive .infinity (fun _ message => some message) fun message =>
        if acknowledged && message == some (.atom "done") then finish else .ok Term.false

@[expose] def initial (mode : NativeFinalizerMode) : Environment :=
  {nativeFinalizerMode := mode, nativeResourceTypes := [NativeResourceArc.typeName CounterResource],
    nativeRefCounter := 5, nativeHeap := [
      (4,NativeResourceArc.handleType CounterResource,.nativeReference 2),
      (3,NativeResourceArc.handleType CounterResource,.nativeReference 2),
      (2,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer 2,NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]),
      (1,NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked",.atom "unpoisoned",NativeCodec.encode ({value := 42#u64} : effects_core.Counter)]),
      (5,"unrelated",.integer 17)]}

/-- Immediate cleanup is conditional on an explicit external timing model. -/
theorem synchronous_interleavings :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 36
      (.start (initial .synchronous) (releaseBoth resource_release_ack 4 inspectHeap)) = true := by cbv

/-- Deferred callbacks retire ownership first, then exactly one dispatcher
executes the actual payload destructor; busy is never accepted as completion. -/
theorem deferred_interleavings :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 64
      (.start (initial .deferred) (releaseBoth resource_release_ack 4 finalizerRace)) = true := by cbv

/-- Release may acknowledge while its destructor is still pending. -/
theorem release_can_precede_cleanup :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 36
      (.start (initial .deferred) (releaseBoth resource_release_ack 4 inspectPending)) = true := by cbv

/-- Reusing one logical owner exhausts verification, rather than modelling UB. -/
theorem repeated_owner_rejected :
    Concurrent.check (fun | .error .exhausted => true | _ => false) 36
      (.start (initial .synchronous) (releaseBoth resource_release_ack 3 inspectHeap)) = true := by cbv

/-- Missing callback timing is never silently assumed to be synchronous. -/
theorem missing_policy_rejected :
    Concurrent.check (fun | .error .exhausted => true | _ => false) 36
      (.start (initial .unspecified) (releaseBoth resource_release_ack 4 inspectHeap)) = true := by cbv

theorem synchronous_schedules (choices : List ScheduleChoice) :
    concurrentFrom (initial .synchronous) (releaseBoth resource_release_ack 4 inspectHeap) choices = .ok Term.true := by
  obtain ⟨_,_,run,final⟩ := Result.run_reaches
    (releaseBoth resource_release_ack 4 inspectHeap) (initial .synchronous) choices
  have checked := Concurrent.check_sound synchronous_interleavings run final
  rw [← concurrentFrom_eq_run] at checked
  split at checked
  · assumption
  · contradiction

theorem deferred_schedules (choices : List ScheduleChoice) :
    concurrentFrom (initial .deferred) (releaseBoth resource_release_ack 4 finalizerRace) choices = .ok Term.true := by
  obtain ⟨_,_,run,final⟩ := Result.run_reaches
    (releaseBoth resource_release_ack 4 finalizerRace) (initial .deferred) choices
  have checked := Concurrent.check_sound deferred_interleavings run final
  rw [← concurrentFrom_eq_run] at checked
  split at checked
  · assumption
  · contradiction
end Reclaim.Properties
