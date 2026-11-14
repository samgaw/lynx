module
public import Record.RepairAppendPrefixInvariant
public import Record.AppendAcknowledgementWitness
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.AppendPrefixWitness
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties Record.RecoveryProperties
open Record.AppendAcknowledgementWitness (original complete)

@[expose] def partialImage : ByteArray := disk (logBytes [13#u16] ++ [19#u8,0#u8])
@[expose] def ones (data : ByteArray) : ByteArray := ⟨(List.replicate data.size (1 : UInt8)).toArray⟩
@[expose] def errorCell : Nat × String × Term := (2,NativeIoError.typeName,.atom "live")
@[expose] def initial (script : Term) : Environment :=
  fileEnv {nativeRefCounter := 2} ⟨1⟩ ⟨original,original,0,script⟩ [errorCell]
@[expose] def effects (visible durable : ByteArray) (position : Nat)
    (config : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile)) : Bool :=
  let env := Record.RepairAppendAcknowledgement.snapshot [] config
  match lookup ⟨1⟩ env with
  | some file => file.visible == visible && file.durable == durable && file.position == position &&
      env.nativeHeap.contains errorCell
  | none => false
@[expose] def failed (visible durable : ByteArray) (position : Nat)
    (config : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile)) : Bool :=
  match config.outcome with
  | .ok (.Err error, file) => error.identity == 2 && file.id == 1 && effects visible durable position config
  | _ => false
@[expose] def blocked (config : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile)) : Bool :=
  match config.outcome with
  | .deadlock => effects partialImage original 6 config
  | _ => false

set_option maxRecDepth 8192 in
/-- Failed rollback may retain a durable partial tail. The actual caller returns
Err and retains the error capability for its caller; it does not promise rollback. -/
theorem resize_error_retains_tail : Concurrent.checkPost (failed partialImage partialImage 6) 256
    (.start (initial (outcome "seek" true 0 (zeroMask original)
      (outcome "write" true 2 (zeroMask original)
        (outcome "set_len" false 2 (ones partialImage) .nil))))
      (append_record_or_rollback ⟨1⟩ 19#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- A failed sync can persist a full unacknowledged record. Error is retained;
the prefix theorem does not replace this outcome with success or rollback. -/
theorem sync_error_can_persist_record : Concurrent.checkPost (failed complete complete 8) 256
    (.start (initial (outcome "seek" true 0 (zeroMask original)
      (outcome "write" true 4 (zeroMask original)
        (outcome "sync_all" false 2 (ones complete) .nil))))
      (append_record_or_rollback ⟨1⟩ 19#u16)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Blocking before rollback leaves the short-write tail and cursor. It is
modelled as a deadlocked wait, not a successful append or an erased operation. -/
theorem blocked_rollback_retains_tail : Concurrent.checkPost blocked 256
    (.start (initial (outcome "seek" true 0 (zeroMask original)
      (outcome "write" true 2 (zeroMask original) (.cons (.atom "blocked") .nil))))
      (append_record_or_rollback ⟨1⟩ 19#u16)) = true := by
  cbv

end Record.AppendPrefixWitness
