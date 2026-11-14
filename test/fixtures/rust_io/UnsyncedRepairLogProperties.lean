module
public import Record.GuardedRepairAdapter
public import Record.RecoveryPrefixWitness
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.UnsyncedRepairLogProperties
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.RecoveryProperties Record.IntegrityProperties Record.RepairCrashProperties
open Record.RecoveryPrefixWitness (image repaired)

@[expose] def longDurable : ByteArray := disk (logBytes [13#u16,19#u16] ++ [7#u8,0#u8,8#u8,0#u8,9#u8,55#u8,66#u8])
@[expose] def complete : ByteArray := disk (logBytes [13#u16,19#u16,23#u16])
@[expose] def appendScript : Term := outcome "seek" true 0 (zeroMask repaired)
  (outcome "write" true 4 (zeroMask repaired) (outcome "sync_all" true 0 ByteArray.empty .nil))
@[expose] def retryScript : Term := outcome "seek" true 0 (zeroMask longDurable)
  (readScript (zeroMask longDurable)
    (outcome "read" true 0 (zeroMask longDurable)
      (outcome "set_len" true 0 (zeroMask longDurable)
        (outcome "sync_all" true 0 ByteArray.empty appendScript))) 8)
@[expose] def failedScript : Term := outcome "seek" true 0 (zeroMask longDurable)
  (readScript (zeroMask longDurable)
    (outcome "set_len" true 0 (zeroMask longDurable)
      (outcome "sync_all" false 4 (zeroMask longDurable) retryScript)) 12)
@[expose] def initialState : State := ⟨image,longDurable,5,failedScript⟩
@[expose] def initial : Environment := Record.GuardedRepairAdapter.pinned
  ({pdict := [(.atom "log",.nativeReference 6)]} : Environment) false initialState

/-- The initial images differ in both contents and length. -/
theorem initial_distinct : image ≠ longDurable := by decide

theorem initial_admitted : Record.ResizeProperties.Admitted initialState := by
  unfold Record.ResizeProperties.Admitted
  decide

theorem initial_visible_prefix : Prefix (disk (logBytes [13#u16])) initialState.visible := by
  change Prefix (disk (logBytes [13#u16]))
    (disk (logBytes [13#u16] ++ (logBytes [19#u16] ++ [7#u8,0#u8,8#u8,0#u8,9#u8])))
  exact Record.RepairCrashProperties.prefix_append _ _

theorem initial_durable_prefix : Prefix (disk (logBytes [13#u16])) initialState.durable := by
  change Prefix (disk (logBytes [13#u16]))
    (disk (logBytes [13#u16] ++ (logBytes [19#u16] ++ [7#u8,0#u8,8#u8,0#u8,9#u8,55#u8,66#u8])))
  exact Record.RepairCrashProperties.prefix_append _ _

@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  let env := Record.RepairingLogProperties.snapshot config
  match config.outcome,lookup ⟨2⟩ env with
  | .ok (.atom "true"),some state =>
      state.visible == complete && state.durable == complete && state.position == 12 &&
      env.nativeRefCounter == 11 &&
      (NativeResourceArc.vmCells Record.GuardedRepairAdapter.payload 3 5 6).all env.nativeHeap.contains &&
      env.nativeHeap.contains (1,NativeMutex.typeName NativeFile,Record.LockedPrefixInvariant.free false) &&
      !env.nativeHeap.any (fun cell => cell.1 == 4 || 7 ≤ cell.1) &&
      env.nativeResourceTypes.contains (NativeResourceArc.typeName shared_log.LogResource)
  | _,_ => false

theorem accepted_outcome (config : Concurrent.Config Term) (checked : accepted config = true) :
    config.outcome = .ok Term.true := by
  unfold accepted at checked
  dsimp only at checked
  split at checked
  · assumption
  · contradiction

end Record.UnsyncedRepairLogProperties
