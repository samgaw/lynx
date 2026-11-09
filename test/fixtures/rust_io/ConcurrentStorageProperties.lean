module
public import Record.ConstructorLogProperties
public import Record.ScheduledLogProperties
public section
open Lynx
namespace Record.ConcurrentStorageProperties

-- Native heap type tags recur in every schedule. Reuse their reflexivity proof
-- rather than expanding byte comparisons for each occurrence in the certificate.
@[cbv_eval] private theorem sameString (value : String) : (value == value) = true := by
  simp

/-- The constructor consumes the real namespace/create/sync script, then the
two mutex-protected writers consume the two full-write/sync sequences. -/
@[expose] def initial : Environment :=
  Record.ConstructorLogProperties.initial {} Record.ScheduledLogProperties.firstInput.script

@[expose] def ordered : ByteArray := ⟨#[13, 0, 242, 255, 19, 0, 236, 255]⟩
@[expose] def reversed : ByteArray := ⟨#[19, 0, 236, 255, 13, 0, 242, 255]⟩

/-- Success requires both acknowledged appends and both complete durable records.
Either serialization order is permitted. Visible buffered bytes alone do not
satisfy this postcondition. -/
@[expose] def durableRecords (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") =>
    let env := match config with
      | .start env _ => env
      | .running state .. => state.nativeView []
    match NativeFile.lookup ⟨2⟩ env with
    | some file => file.durable == ordered || file.durable == reversed
    | none => false
  | _ => false

theorem accepted_outcome (config : Concurrent.Config Term)
    (accepted : durableRecords config = true) : config.outcome = .ok Term.true := by
  unfold durableRecords at accepted
  split at accepted
  · assumption
  · contradiction

end Record.ConcurrentStorageProperties
