module
public import Errors.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Errors.Properties
set_option maxRecDepth 4096
set_option maxHeartbeats 4000000
attribute [local cbv_eval] Term.compare_atoms

/-- Independently owned, admitted OS errors are destroyed by actual Rust bodies.
The mailbox joins the workers before inspecting their shared capability heap. -/
@[expose] def destroyBoth
    (explicit : NativeIoError → NativeM Bool)
    (implicit : NativeIoError → NativeM Unit) : Result Term :=
  Result.schedule {} (do
    implicit ⟨1⟩
    Result.send [] (.atom "done") (.ok .nil)) fun _ => do
      let acknowledged ← explicit ⟨2⟩
      Result.receive .infinity (fun _ message => some message) fun message =>
        .nativeGet fun env =>
          match env.nativeHeap with
          | [(3,"unrelated",.integer payload)] => .ok (
              if acknowledged && message == some (.atom "done") && payload == 17 &&
                env.nativeRefCounter == 3 then Term.true else Term.false)
          | _ => .ok Term.false

@[expose] def admitted : Environment :=
  {nativeRefCounter := 3, nativeHeap :=
    [(1, NativeIoError.typeName, .atom "live"), (2, NativeIoError.typeName, .atom "live"),
      (3,"unrelated",.integer 17)]}

/-- Every transition order consumes both tokens, preserving an unrelated cell and the identity supply. -/
theorem every_interleaving (elapsed : PID → Nat → Nat) :
    Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 24
      (.start admitted (destroyBoth discard_error_ack io_core.discard_io_error_implicit) elapsed) = true := by
  cbv

/-- Every actual run consumes both admitted error capabilities while preserving
its unrelated cell, for arbitrary elapsed-time functions. -/
theorem every_run :
    concurrentFrom admitted
      (destroyBoth discard_error_ack io_core.discard_io_error_implicit) (.ok Term.true) := by
  intro elapsed events last outcome run terminal
  have checked := Concurrent.check_sound (every_interleaving elapsed) run terminal
  split at checked
  · rfl
  · contradiction
end Errors.Properties
