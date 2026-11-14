module
public import Record.GuardedRepairAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConcurrentRepairLogProperties
open NativeFile Record.Properties Record.LogProperties Record.CrashProperties Record.GuardedRepairAdapter

/-- Two callers start with an already allocated VM resource and no remaining
I/O error capability. The script admits either serial append order. -/
@[expose, instance_reducible] def admission : Admission := ⟨42,by decide,false⟩
@[expose] def initial : Environment := @pinned admission
  ({pdict := [(.atom "log",.nativeReference 6)]} : Environment) false
  ⟨Record.RepairingLogProperties.torn,Record.RepairingLogProperties.torn,0,
    Record.RepairingLogProperties.fileScript⟩

@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  let env := Record.RepairingLogProperties.snapshot config
  match config.outcome,lookup ⟨2⟩ env with
  | .ok (.atom "true"),some state =>
      (state.visible == disk (logBytes [13#u16,19#u16,23#u16]) ||
        state.visible == disk (logBytes [13#u16,23#u16,19#u16])) &&
      state.visible == state.durable && state.position == 12 && env.nativeRefCounter == 46 &&
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

end Record.ConcurrentRepairLogProperties
