module
public import Returned.Properties
public import Returned.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Returned.Properties

theorem facade (value : Bool) : __FACADE__ value = ownership_app.returned_guard_flip value := rfl

set_option maxHeartbeats 1000000 in
theorem adapter_next {β : Type} (value : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do let result ← Rustler.executeNative (__FACADE__ value) Rustler.encodeBool
        next result).run {} schedule =
      (next (Rustler.encodeBool (!value))).run {nativeRefCounter := 3} schedule := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [facade, Rustler.executeNative, Result.handle, Result.bind, ownership_app.returned_guard_flip,
      protocol, toggle, NativeMutex.new, NativeMutex.lock, NativeMutex.try_lock,
      NativeMutex.tryAcquire, NativeMutex.pollLock, NativeMutex.typeName,
      NativeCodec.decode, NativeCodec.encode, NativeDrop.drop, NativeMutex.dispose,
      NativeM.allocate, NativeM.removeCell, NativeM.readCell, NativeGuard.release,
      NativeGuard.pollRelease, NativeGuard.deref, NativeGuard.deref_mut,
      NativePoisonError.into_inner, NativeM.ok, NativeM.lift, Result.wait_run,
      Result.ofExcept, Result.nativeModify_bind, Result.nativeGet_bind]

end Returned.Properties
