module
public import Lynx
public import GuardedSync.Properties
public import GuardedSync.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedSync.NifProperties

theorem open_contract : __OPEN__ = (do
    let opened ← io_protocol.open_readwrite (toStr "journal")
    match opened with
    | .Ok file => do
      let mutex ← NativeMutex.new file
      let owner ← NativeResourceArc.newOwned ({file := mutex} : shared_log.LogResource)
      NativeM.ok (.Ok owner)
    | .Err error => do
      NativeIoError.dispose error
      NativeM.ok (.Err (Rustler.atomErrorOutcome "open_failed"))) := by
  simp [__OPEN__,
    NativeOwnedDrop.drop, NativeM.ok, GuardedSync.Extraction.ErrorConstants.literal_0]
  rfl

theorem sync_contract (owner : NativeResourceArc shared_log.LogResource)
    (first second : U8) (resume : Bool) :
    __SYNC__ owner first second resume = (do
      let payload ← NativeResourceArc.deref owner
      let result ← io_protocol.poll_locked_sync payload.file (Array.make 2#usize [first, second]) resume
      NativeResourceArc.releaseOwned owner
      match result with
      | none => NativeM.ok (.Ok none)
      | some (.Err error) => NativeM.ok (.Err error)
      | some (.Ok count) => NativeM.ok (.Ok (some (UScalar.cast .U64 count)))) := by
  simp [__SYNC__,
    NativeOwnedDrop.drop, NativeM.ok, NativeM.lift]
  congr 1
  funext payload
  congr 1
  funext result
  cases result with
  | none => rfl
  | some reply => cases reply <;> rfl


end GuardedSync.NifProperties
