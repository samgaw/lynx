module
public import Rw.Properties
public import Rw.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Rw.Properties

theorem facade (value : Bool) : __FACADE__ value = rw_probe value := by
  simp [__FACADE__]

set_option maxHeartbeats 1000000 in
theorem adapter_next {β : Type} (value : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do let encoded ← Rustler.executeNative (__FACADE__ value) Rustler.encodeBool
        next encoded).run initial schedule =
      (next (Rustler.encodeBool (!value))).run {initial with nativeRefCounter := 5} schedule := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [facade, Rustler.executeNative, Result.wait_run, Result.handle, Result.bind, rw_probe, toggle_app, initial, NativeRwLock.new, NativeRwLock.read, NativeRwLock.pollRead, NativeRwLock.pollWrite, NativeRwLock.prepareWrite,
      NativeRwLock.writerWaiting, NativeRwLock.writerRequestType,
      NativeRwLock.write, NativeRwLock.acquireRead, NativeRwLock.acquireWrite,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwLock.state, NativeRwLock.store, NativeRwLock.contents,
      NativeRwLock.decodeState, NativeRwLock.decodeLease, NativeRwLock.lease,
      NativeRwLock.readerLimit, NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut,
      NativeDrop.drop, NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      NativeCodec.encode, NativeCodec.decode, NativeRwLock.typeName,
      Result.nativeModify_bind, Result.nativeModify_run, Result.ofExcept, List.eraseDups_cons, List.eraseDups_nil, NativeCodec.typeName,
      Result.ok_bind, Result.nativeGet_bind]

end Rw.Properties
