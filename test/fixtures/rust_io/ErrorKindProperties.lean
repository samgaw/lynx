module
public import IoKinds.Extraction.Funs
public section
open Aeneas Aeneas.Std io_protocol
namespace IoKinds.Properties

@[expose] def truncated : core.io.error.ErrorKind → Bool
  | .UnexpectedEof => true
  | _ => false

/-- Classify every extracted standard error variant, not only selected examples. -/
theorem core_spec (kind : core.io.error.ErrorKind) :
    io_core.is_truncated kind = RustM.ok (truncated kind) := by
  cases kind <;>
    simp [io_core.is_truncated, core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq,
      truncated, io_core.TRUNCATED_INPUT, core.io.error.ErrorKind.read_discriminant]

/-- The caller uses the actual first-party dependency and standard comparison. -/
theorem composition (kind : core.io.error.ErrorKind) :
    truncated_input kind = RustM.ok (truncated kind) := by
  simp only [truncated_input, core_spec]

/-- Retryable interruption must not be mistaken for truncation. -/
theorem interruption : truncated_input .Interrupted = RustM.ok false := by
  exact composition .Interrupted

end IoKinds.Properties
