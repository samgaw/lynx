module
public import Record.RepairAppendPrefixInvariant
public import Record.RecoveryPrefixWitness
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairPrefixWitness
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties Record.RecoveryProperties
  Record.IntegrityProperties
open Record.RecoveryPrefixWitness (image repaired script)

abbrev Reply := core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile
@[expose] def errorCell : Nat × String × Term := (2,NativeIoError.typeName,.atom "live")
@[expose] def ones (data : ByteArray) : ByteArray := ⟨(List.replicate data.size (1 : UInt8)).toArray⟩
@[expose] def initial (choices : Term) : Environment :=
  fileEnv {nativeRefCounter := 2} ⟨1⟩ ⟨image,image,5,choices⟩ [errorCell]
@[expose] def effects (visible durable : ByteArray) (position : Nat) (config : Concurrent.Config Reply) : Bool :=
  let env := Record.RepairAppendAcknowledgement.snapshot [] config
  match lookup ⟨1⟩ env with
  | some state => state.visible == visible && state.durable == durable && state.position == position &&
      env.nativeHeap.contains errorCell
  | none => false
@[expose] def failed (visible durable : ByteArray) (position : Nat) (config : Concurrent.Config Reply) : Bool :=
  match config.outcome with
  | .ok (.Err error,file) => error.identity == 2 && file.id == 1 && effects visible durable position config
  | _ => false
@[expose] def blocked (visible durable : ByteArray) (config : Concurrent.Config Reply) : Bool :=
  match config.outcome with
  | .deadlock => effects visible durable 12 config
  | _ => false

set_option maxRecDepth 8192 in
/-- A failed actual read retains the five bytes already consumed and the
original images; no repair acknowledgement or resize is fabricated. -/
theorem read_error_retains_cursor : Concurrent.checkPost (failed image image 5) 256
    (.start (initial (script 5 (outcome "read" false 2 (zeroMask image) .nil)))
      (repair_log ⟨1⟩ 4#usize)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Failed truncation retains the actual malformed suffix and the parser's
cursor. The returned error capability remains live for the caller. -/
theorem resize_error_retains_suffix : Concurrent.checkPost (failed image image 12) 256
    (.start (initial (script 12 (outcome "set_len" false 2 (zeroMask image) .nil)))
      (repair_log ⟨1⟩ 4#usize)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Failed synchronization can nevertheless persist the truncation. Both the
real error and the beyond-EOF cursor are retained. -/
theorem sync_error_persists_resize : Concurrent.checkPost (failed repaired repaired 12) 256
    (.start (initial (script 12 (outcome "set_len" true 0 (zeroMask image)
      (outcome "sync_all" false 2 (ones repaired) .nil)))) (repair_log ⟨1⟩ 4#usize)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Blocking before truncation retains the complete original suffix. -/
theorem blocked_before_resize : Concurrent.checkPost (blocked image image) 256
    (.start (initial (script 12 (.cons (.atom "blocked") .nil)))
      (repair_log ⟨1⟩ 4#usize)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Blocking after truncation retains distinct visible/durable lengths. It is a
deadlocked wait, not a successful sync or restoration of the earlier image. -/
theorem blocked_before_sync : Concurrent.checkPost (blocked repaired image) 256
    (.start (initial (script 12 (outcome "set_len" true 0 (zeroMask image)
      (.cons (.atom "blocked") .nil)))) (repair_log ⟨1⟩ 4#usize)) = true := by
  cbv

end Record.RepairPrefixWitness
