module
public import Record.RepairAcknowledgement

public section

open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol

namespace Record.NamedRepairAcknowledgement
open NativeFile
open Record.FileView (namedWorld NamedSeparated named_inode named_render named_separated)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.RepairCrashProperties (LogImage)
open Record.ResizeProperties (Admitted)
open Record.RepairImageInvariant (Reply)

/-- The extracted repair returns the original acknowledged records, using
the real writable descriptor and shared inode model. The input bytes,
cursor, record budget, and read/resize/sync host script can vary. -/
theorem named_acknowledges (number : Nat) (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile)
    (separate : NamedSeparated number file frame) (admitted : Admitted before)
    (stable : before.durable = before.visible) (visible : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event) (last : Concurrent.Config Reply)
    (executed : Concurrent.Run (.start (namedWorld number env file before frame)
      (repair_log file maxRecords) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok (some returned), returnedFile))) :
    returnedFile = file ∧ returned.val = values ∧ ∃ after,
      last = .start (namedWorld number env file after frame)
        (.ok (.Ok (some returned), returnedFile)) elapsed ∧
      inode number (namedWorld number env file after frame) =
        some ⟨disk (logBytes values), disk (logBytes values), 0, .nil⟩ ∧
      lookup file (namedWorld number env file after frame) = some after := by
  have admittedFrame := (named_separated number file frame).mpr separate
  have ran : Concurrent.Run
      (.start (@Record.FileView.render (Record.FileView.named number) env file before frame)
        (repair_log file maxRecords) elapsed) events last := by
    simpa only [named_render] using executed
  obtain ⟨sameFile, records, after, ending, v, d, valid⟩ :=
    Record.RepairAcknowledgement.repair_run_acknowledges (view := Record.FileView.named number)
      env file frame before values maxRecords returned returnedFile
      admittedFrame admitted stable visible elapsed events last ran terminal
  rw [named_render] at ending
  refine ⟨sameFile, records, after, ending, ?_, ?_⟩
  · rw [named_inode number env file after frame separate valid, v, d]
  · simpa only [named_render] using
      (@Record.FileView.load_rendered (Record.FileView.named number)) env file after frame admittedFrame valid

end Record.NamedRepairAcknowledgement
