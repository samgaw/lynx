module
public import FileAwait.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace FileAwait.Task
open Properties

/-- Adapts Poll's shape; execution remains the extracted Rust poll body. -/
@[expose] def poll (state : suspended_write.closure) (context : NativeTaskContext) :
    NativeM (NativeTask.Step Reply suspended_write.closure) := do
  let (reply, future, context) ← suspended_write.closure.poll ⟨state⟩ context
  match reply with
  | .Pending => NativeM.ok (.pending future.pointer context)
  | .Ready value => NativeM.ok (.ready value future.pointer)

@[expose] def registered (env : Environment) (notified : Bool) : Environment :=
  {env with nativeHeap := env.nativeHeap ++
    [(0, NativeWaker.typeName, .atom (if notified then "notified" else "idle"))]}

@[expose] def result (cancel : Bool) (config : Concurrent.Config (Option Reply)) : Bool :=
  let returned := match config.outcome with
    | .ok none => cancel
    | .ok (some (.Ok count)) => !cancel && count.val == 1
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  returned && env.nativeHeap == (registered closed cancel).nativeHeap &&
    env.nativeRefCounter == 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem driven_file_cleanup (cancel : Bool) :
    Concurrent.checkPost (result cancel) 256
      (.start (registered before false)
        (NativeTask.drive poll suspended_write.closure.drop_owned (fun _ => cancel)
          ⟨⟨0, false⟩⟩ 2 (initial ⟨1⟩ input))) = true := by
  set_option cbv.maxSteps 8000000 in cases cancel <;> cbv

theorem every_driven_exit (cancel : Bool)
    (run : Concurrent.Run (.start (registered before false)
      (NativeTask.drive poll suspended_write.closure.drop_owned (fun _ => cancel)
        ⟨⟨0, false⟩⟩ 2 (initial ⟨1⟩ input))) events last)
    (terminal : Concurrent.Terminal last returned) : result cancel last = true :=
  Concurrent.checkPost_sound (driven_file_cleanup cancel) run terminal

/-- Exhausting the poll budget retains the live frame's file and completed write;
it cannot establish completion, cancellation or an implicit destructor. -/
@[expose] def cutoff (config : Concurrent.Config (Option Reply)) : Bool :=
  let exhausted := match config.outcome with
    | .error .exhausted => true
    | _ => false
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  exhausted && env.nativeHeap == (registered written false).nativeHeap &&
    env.nativeRefCounter == 1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
theorem one_poll_cutoff :
    Concurrent.checkPost cutoff 256
      (.start (registered before false)
        (NativeTask.drive poll suspended_write.closure.drop_owned (fun _ => false)
          ⟨⟨0, false⟩⟩ 1 (initial ⟨1⟩ input))) = true := by
  set_option cbv.maxSteps 8000000 in cbv

end FileAwait.Task
