module
public import TryLock.Properties
public import TryLock.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace TryLock.Properties

@[expose] def encode (value : Bool × Bool × Bool × Bool) : Term :=
  .tuple #[Rustler.encodeBool value.1, Rustler.encodeBool value.2.1,
    Rustler.encodeBool value.2.2.1, Rustler.encodeBool value.2.2.2]

theorem facade (value : Bool) : __FACADE__ value = ownership_app.try_cycle value := rfl

set_option maxHeartbeats 1000000 in
theorem adapter_next {β : Type} (value : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do let result ← Rustler.executeNative (__FACADE__ value) encode
        next result).run {} schedule =
      (next (encode (false, value, true, !value))).run {nativeRefCounter := 4} schedule := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [facade, Rustler.executeNative, Result.handle, Result.bind, ownership_app.try_cycle,
      ownership_base.try_toggle, toggle, NativeMutex.new, NativeMutex.lock,
      NativeMutex.try_lock, NativeMutex.tryAcquire, NativeMutex.pollLock,
      NativeMutex.typeName, NativeCodec.decode, NativeCodec.encode,
      NativeDrop.drop, NativeMutex.dispose, NativeM.allocate, NativeM.removeCell, NativeM.readCell,
      NativeGuard.release, NativeGuard.pollRelease, NativeGuard.deref,
      NativeGuard.deref_mut, NativePoisonError.into_inner, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeGet_bind]

end TryLock.Properties
