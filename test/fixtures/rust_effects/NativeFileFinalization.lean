module
public import FileResource.Model
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Finalization
set_option maxRecDepth 4096
set_option maxHeartbeats 16000000
set_option cbv.maxSteps 2000000

@[expose] def closeChoice (status : String) : Term :=
  .cons (.tuple #[.atom "close", .atom status, .integer (if status == "error" then 5 else 0), .bitstring ⟨#[0]⟩ 0]) .nil

@[expose] def fileState (script : Term) : NativeFile.State :=
  ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, script⟩

@[expose] def initial (script : Term) : Environment :=
  {nativeFinalizerMode := .deferred, nativeRefCounter := 4,
    nativeResourceTypes := [NativeResourceArc.typeName FileResource], nativeHeap := [
      (3, NativeResourceArc.handleType FileResource, .nativeReference 2),
      (2, NativeResourceArc.typeName FileResource,
        .tuple #[.integer 1, NativeCodec.encode FileResource.Properties.payload]),
      FileResource.Properties.fileCell (fileState script), (4, "unrelated", .integer 17)]}

@[expose] def inspectClosed : Result Term :=
  .nativeGet fun env =>
    match NativeFile.lookupClosed ⟨1⟩ env with
    | none => .ok Term.false
    | some state => .ok (if state.visible.data == #[2] && state.durable.data == #[1] &&
        state.script == .nil && env.nativeRefCounter == 4 &&
        env.nativeHeap.length == 2 &&
        env.nativeHeap.any (fun cell => cell == (4, "unrelated", .integer 17)) then
          Term.true else Term.false)

@[expose] def awaitRunning : Result Unit :=
  .wait (fun env => if env.nativeHeap.any (fun cell =>
      cell.1 == 2 && cell.2.1 == NativeResourceArc.runningFinalizerType FileResource) then
        some (.ok (), env) else none) Result.ofExcept

/-- An explicit external completion action makes a blocked close ready. It
preserves the callback marker and every unrelated cell. This is not a VM thread. -/
@[expose] def resumeClose : Result Unit :=
  .nativeModify (fun env =>
    match NativeFile.lookup ⟨1⟩ env with
    | some state =>
      match state.script with
      | .cons (.atom "blocked") rest =>
        (Except.ok (), NativeFile.store ⟨1⟩ {state with script := rest} env)
      | _ => (Except.error .exhausted, env)
    | none => (Except.error .exhausted, env))
    Result.ofExcept

@[expose] def suspendedRace (release : NativeResourceArc FileResource → NativeM Bool) : Result Term := do
  let acknowledged ← release ⟨2,3⟩
  if !acknowledged then return Term.false
  Result.schedule {} (do
    let status ← NativeResourceArc.runFinalizer (α := FileResource) 2
    Result.send [] (match status with | .completed => .atom "completed" | _ => .atom "wrong") (.ok .nil)) fun _ => do
      awaitRunning
      let status ← NativeResourceArc.runFinalizer (α := FileResource) 2
      match status with
      | .busy =>
        let openFile ← Result.nativeGet fun env => .ok ((NativeFile.lookup ⟨1⟩ env).isSome)
        if !openFile then return Term.false
        resumeClose
        Result.receive .infinity (fun _ message => some message) fun message =>
          if message == some (.atom "completed") then inspectClosed else .ok Term.false
      | _ => .ok Term.false

@[expose] def closeOnce (release : NativeResourceArc FileResource → NativeM Bool) : Result Term := do
  let acknowledged ← release ⟨2,3⟩
  if !acknowledged then return Term.false
  let status ← NativeResourceArc.runFinalizer (α := FileResource) 2
  match status with
  | .completed => inspectClosed
  | _ => .ok Term.false

/-- A waiting real file destructor remains busy, then completes once after the
explicit host-completion action. Close does not synchronize the dirty byte. -/
theorem suspended_cleanup_interleavings :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 64
      (.start (initial (.cons (.atom "blocked") (closeChoice "ok"))) (suspendedRace file_resource_release_ack)) = true := by cbv

/-- Rust's file destructor ignores a reported close error and consumes ownership;
that is distinct from a successful fsync or a reusable file descriptor. -/
theorem close_error_consumes_file :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 32
      (.start (initial (closeChoice "error")) (closeOnce file_resource_release_ack)) = true := by cbv

/-- An absent close outcome cannot count as a completed callback. -/
theorem missing_close_rejected :
    Concurrent.check (fun | .error .exhausted => true | _ => false) 32
      (.start (initial .nil) (closeOnce file_resource_release_ack)) = true := by cbv

/-- Inspect interpreter failure directly; verification exhaustion cannot be
caught as an Erlang exception or turned into a successful native return. -/
@[expose] def interrupted : Environment :=
  {initial .nil with nativeHeap := [
    (2, NativeResourceArc.runningFinalizerType FileResource, .atom "running"),
    FileResource.Properties.fileCell (fileState .nil), (4, "unrelated", .integer 17)]}

attribute [local cbv_eval] Result.nativeModify_run Result.nativeGet_continuation_run
  Result.nativeSet_continuation_run Result.ok_apply Result.error_apply

theorem interrupted_cleanup_retains_state (choices : List ScheduleChoice) :
    (closeOnce file_resource_release_ack).run (initial .nil) choices =
      (.error .exhausted, interrupted) := by
  cbv
  rw [Result.wait_ready_run (NativeFile.pollClose ⟨1⟩) _ _ interrupted (.error .exhausted) (by cbv) choices]
  cbv

/-- No eventual completion is inferred for a permanently blocked destructor. -/
theorem blocked_close_not_completed :
    Concurrent.check (fun | .deadlock => true | _ => false) 32
      (.start (initial (.cons (.atom "blocked") .nil)) (closeOnce file_resource_release_ack)) = true := by cbv

theorem suspended_cleanup_schedules (choices : List ScheduleChoice) :
    concurrentFrom (initial (.cons (.atom "blocked") (closeChoice "ok"))) (suspendedRace file_resource_release_ack) choices = .ok Term.true := by
  obtain ⟨_, _, run, final⟩ := Result.run_reaches (suspendedRace file_resource_release_ack)
    (initial (.cons (.atom "blocked") (closeChoice "ok"))) choices
  have checked := Concurrent.check_sound suspended_cleanup_interleavings run final
  rw [← concurrentFrom_eq_run] at checked
  split at checked
  · assumption
  · contradiction
end FileResource.Finalization
