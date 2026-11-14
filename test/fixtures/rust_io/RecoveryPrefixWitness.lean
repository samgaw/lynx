module
public import Record.RepairPrefixReturn
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RecoveryPrefixWitness
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.IntegrityProperties Record.RecoveryProperties

/-- An acknowledged record, another complete unacknowledged record, a malformed
complete record and a final byte. This suffix is longer than a partial record. -/
@[expose] def image : ByteArray := disk (logBytes [13#u16,19#u16] ++ [7#u8,0#u8,8#u8,0#u8,9#u8])
@[expose] def repaired : ByteArray := disk (logBytes [13#u16,19#u16])
@[expose] def script (reads : Nat) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask image) (readScript (zeroMask image) rest reads)

@[expose] def recovered (config : Concurrent.Config (core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile)) : Bool :=
  let env := Record.RepairAppendAcknowledgement.snapshot [] config
  match config.outcome, NativeFile.lookup ⟨1⟩ env with
  | .ok (.Ok values,file), some state => values.val == [13#u16,19#u16] && file.id == 1 &&
      state.visible == image && state.durable == image && state.position == 12 && state.script == .nil
  | _,_ => false

@[expose] def repairedResult (capped : Bool)
    (config : Concurrent.Config (core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile)) : Bool :=
  let env := Record.RepairAppendAcknowledgement.snapshot [] config
  match config.outcome, NativeFile.lookup ⟨1⟩ env with
  | .ok (.Ok result,file), some state =>
      file.id == 1 && state.script == .nil &&
      if capped then result.isNone && state.visible == image && state.durable == image && state.position == 4
      else (result.map (·.val)) == some [13#u16,19#u16] && state.visible == repaired &&
        state.durable == repaired && state.position == 12
  | _,_ => false

set_option maxRecDepth 8192 in
/-- Actual parsing retains the extra valid record and stops at the malformed
record; the unchanged file and cursor are checked too. -/
theorem scans_extra_record : Concurrent.checkPost recovered 256
    (.start (fileEnv {} ⟨1⟩ ⟨image,image,5,script 12 .nil⟩ []) (recover_log ⟨1⟩ 4#usize)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- Actual repair retains both valid records and synchronizes the truncation,
with its actual beyond-EOF cursor. -/
theorem repairs_arbitrary_suffix : Concurrent.checkPost (repairedResult false) 256
    (.start (fileEnv {} ⟨1⟩ ⟨image,image,5,script 12
      (outcome "set_len" true 0 (zeroMask image) (outcome "sync_all" true 0 ByteArray.empty .nil))⟩ [])
      (repair_log ⟨1⟩ 4#usize)) = true := by
  cbv

set_option maxRecDepth 8192 in
/-- A capped scan returns None without resizing or syncing the unread suffix. -/
theorem capped_retains_suffix : Concurrent.checkPost (repairedResult true) 256
    (.start (fileEnv {} ⟨1⟩ ⟨image,image,5,script 4 .nil⟩ []) (repair_log ⟨1⟩ 1#usize)) = true := by
  cbv

end Record.RecoveryPrefixWitness
