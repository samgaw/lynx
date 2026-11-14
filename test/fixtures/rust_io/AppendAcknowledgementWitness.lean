module
public import Record.RepairAppendAcknowledgement
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.AppendAcknowledgementWitness
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.RecoveryProperties Record.RepeatedRepairProperties

@[expose] def original : ByteArray := disk (logBytes [13#u16])
@[expose] def complete : ByteArray := disk (logBytes [13#u16,19#u16])
@[expose] def torn : ByteArray := disk (logBytes [13#u16] ++ [7#u8])
@[expose] def appendScript (data : ByteArray) (amount : Nat) (rollback : Bool) : Term :=
  outcome "seek" true 0 (zeroMask data)
    (outcome "write" true amount (zeroMask data)
      (if rollback then outcome "set_len" true 0 (zeroMask data)
        (outcome "sync_all" true 0 ByteArray.empty .nil)
      else outcome "sync_all" true 0 ByteArray.empty .nil))

@[expose] def accepted (ack : Bool) (expected : ByteArray) (position : Nat)
    (config : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile)) : Bool :=
  let env := Record.RepairAppendAcknowledgement.snapshot [] config
  match config.outcome, NativeFile.lookup ⟨1⟩ env with
  | .ok (.Ok answer, returned), some file => answer == ack && returned.id == 1 &&
      file.visible == expected && file.durable == expected && file.position == position && file.script == .nil
  | _, _ => false

set_option maxRecDepth 8192 in
/-- This actual append can acknowledge even when the initial visible prefix has
not yet been persisted. Synchronization, not initial stability, establishes it. -/
theorem full_acknowledges : Concurrent.checkPost (accepted true complete 8) 256
    (.start (fileEnv {} ⟨1⟩ ⟨original,ByteArray.empty,3,appendScript ByteArray.empty 4 false⟩ [])
      (append_record_or_rollback ⟨1⟩ 19#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- False is a successful synchronized rollback, retaining the beyond-EOF
cursor from the actual short write. It is not an append acknowledgement. -/
theorem short_rolls_back : Concurrent.checkPost (accepted false original 6) 256
    (.start (fileEnv {} ⟨1⟩ ⟨original,ByteArray.empty,3,appendScript ByteArray.empty 2 true⟩ [])
      (append_record_or_rollback ⟨1⟩ 19#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- The actual composed caller reaches its true return after reading a complete
record and torn tail, repairing, appending, and synchronizing both operations. -/
theorem repair_acknowledges : Concurrent.checkPost (accepted true complete 8) 256
    (.start (fileEnv {} ⟨1⟩ ⟨torn,torn,3,repairScript torn (appendScript original 4 false)⟩ [])
      (repair_and_append ⟨1⟩ 4#usize 19#u16)) = true := by
  cbv

end Record.AppendAcknowledgementWitness
