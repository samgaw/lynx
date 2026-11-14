module
public import Record.LockedPrefixWitness
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.UnsyncedRepairWitness
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.RecoveryProperties Record.IntegrityProperties Record.LockedPrefixWitness
open Record.RecoveryPrefixWitness (image repaired)

@[expose] def shortDurable : ByteArray := disk (logBytes [13#u16])
@[expose] def longDurable : ByteArray := disk (logBytes [13#u16,19#u16] ++ [7#u8,0#u8,8#u8,0#u8,9#u8,55#u8,66#u8])
@[expose] def initial (durable : ByteArray) (choices : Term) : Environment :=
  Record.LockedPrefixInvariant.view {} 9 frame (Record.LockedPrefixInvariant.free true)
    ⟨image,durable,5,choices⟩
@[expose] def scan (durable : ByteArray) (reads : Nat) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask durable) (readScript (zeroMask durable) rest reads)
@[expose] def append : Term := outcome "seek" true 0 (zeroMask repaired)
  (outcome "write" true 4 (zeroMask repaired) (outcome "sync_all" true 0 ByteArray.empty .nil))
@[expose] def successful (durable : ByteArray) : Term := scan durable 12
  (outcome "set_len" true 0 (zeroMask durable) (outcome "sync_all" true 0 ByteArray.empty append))

set_option maxRecDepth 8192 in
/-- Unacknowledged visible records survive parsing while the shorter durable
image is retained until synchronization; the actual guarded append then commits. -/
theorem shorter_durable_success : Concurrent.checkPost accepted 512
    (.start (initial shortDurable (successful shortDurable))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by cbv

set_option maxRecDepth 8192 in
/-- A durable suffix longer than the current visible image is also admitted. -/
theorem longer_durable_success : Concurrent.checkPost accepted 512
    (.start (initial longDurable (successful longDurable))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by cbv

set_option maxRecDepth 8192 in
/-- A failed sync keeps the actual longer durable suffix, released guard and
advanced cursor; it is not reported as a successful append. -/
theorem longer_durable_sync_error : Concurrent.checkPost (failed repaired longDurable 12) 256
    (.start (initial longDurable (scan longDurable 12 (outcome "set_len" true 0 (zeroMask longDurable)
      (outcome "sync_all" false 4 (zeroMask longDurable) .nil))))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by cbv

set_option maxRecDepth 8192 in
/-- Read failure retains both unequal images and the actual partial cursor. -/
theorem shorter_durable_read_error : Concurrent.checkPost (failed image shortDurable 5) 256
    (.start (initial shortDurable (scan shortDurable 5
      (outcome "read" false 4 (zeroMask shortDurable) .nil)))
      (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by cbv

@[expose] def blocked (config : Concurrent.Config (core.result.Result Bool NativeIoError)) : Bool :=
  match config.outcome with
  | .deadlock => effects true true repaired longDurable 12 config
  | _ => false

set_option maxRecDepth 8192 in
/-- Blocked synchronization retains distinct images and the held poisoned guard. -/
theorem longer_durable_blocked : Concurrent.checkPost blocked 256
    (.start (initial longDurable (scan longDurable 12 (outcome "set_len" true 0 (zeroMask longDurable)
      (.cons (.atom "blocked") .nil)))) (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) = true := by cbv

end Record.UnsyncedRepairWitness
