module
public import Record.RepairWriterObserver
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.ConcurrentRepairWriterInvariant
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.ResizeProperties Record.RepairCrashProperties Record.RepeatedRepairProperties
  Record.RecoveryProperties Record.RepairWriterObserver

@[expose] def original : ByteArray := disk (logBytes [13#u16])
@[expose] def torn : ByteArray := disk (logBytes [13#u16] ++ [7#u8])
@[expose] def firstOnly : ByteArray := disk (logBytes [13#u16, 19#u16])
@[expose] def secondOnly : ByteArray := disk (logBytes [13#u16, 23#u16])
@[expose] def ordered : ByteArray := disk (logBytes [13#u16, 19#u16, 23#u16])
@[expose] def reversed : ByteArray := disk (logBytes [13#u16, 23#u16, 19#u16])

/-- Persistence keeps the preceding durable length until the actual sync.
The second caller's script depends on byte length, not the first payload. -/
@[expose] def appendScript (data : ByteArray) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask data)
    (outcome "write" true 4 (zeroMask data)
      (outcome "sync_all" true 0 ByteArray.empty rest))
@[expose] def fileScript : Term := repairScript torn
  (appendScript original (repairScript firstOnly (appendScript firstOnly .nil)))
@[expose] def initial : Environment :=
  fileEnv {} ⟨2⟩ ⟨torn, torn, 0, fileScript⟩ [
    (1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2]),
    (0, ackTag, .nil)]

@[expose] def snapshot : Concurrent.Config Term → Environment
  | .start env .. => env
  | .running state .. => state.nativeView []
@[expose] def admittedBytes (data : ByteArray) : Bool :=
  data == torn || data == original || data == firstOnly || data == secondOnly || data == ordered || data == reversed
@[expose] def containsFirst (data : ByteArray) : Bool :=
  data == firstOnly || data == ordered || data == reversed
@[expose] def containsSecond (data : ByteArray) : Bool :=
  data == secondOnly || data == ordered || data == reversed
@[expose] def firstProtected (visible durable : ByteArray) : Bool :=
  ((visible == firstOnly || visible == ordered) && (durable == firstOnly || durable == ordered)) ||
    (visible == reversed && durable == reversed)
@[expose] def secondProtected (visible durable : ByteArray) : Bool :=
  ((visible == secondOnly || visible == reversed) && (durable == secondOnly || durable == reversed)) ||
    (visible == ordered && durable == ordered)
@[expose] def bothProtected (visible durable : ByteArray) : Bool :=
  (visible == ordered && durable == ordered) || (visible == reversed && durable == reversed)
@[expose] def retained (config : Concurrent.Config Term) : Bool :=
  let env := snapshot config
  match NativeFile.lookup ⟨2⟩ env with
  | some file => admittedBytes file.visible && admittedBytes file.durable &&
      (!acknowledged 19 env || firstProtected file.visible file.durable) &&
      (!acknowledged 23 env || secondProtected file.visible file.durable) &&
      (!(acknowledged 19 env && acknowledged 23 env) || bothProtected file.visible file.durable)
  | none => false
@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  let env := snapshot config
  match config.outcome, NativeFile.lookup ⟨2⟩ env with
  | .ok (.atom "true"), some file =>
    ((file.visible == ordered && file.durable == ordered) ||
      (file.visible == reversed && file.durable == reversed)) &&
    acknowledged 19 env && acknowledged 23 env &&
    env.nativeHeap.contains (1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2])
  | _, _ => false
@[expose] def safe (config : Concurrent.Config Term) : Bool :=
  retained config && (!config.successors.isEmpty || accepted config)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 256000000 in
/-- Every raw prefix preserves old and observed new acknowledgements; every
terminal interleaving has both complete records in a permitted serial order. -/
theorem prefixes_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 256 (.start initial
      (callers (locked_repair_and_append ⟨1⟩ 4#usize 19#u16)
        (locked_repair_and_append ⟨1⟩ 4#usize 23#u16)) elapsed) = true := by
  set_option cbv.maxSteps 128000000 in cbv

end Record.ConcurrentRepairWriterInvariant
