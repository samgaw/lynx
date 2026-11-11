module
public import TryRw.Properties
public import TryRw.RustlerBridge
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace TryRw.Properties

@[expose] def encode (value : Bool × Bool × Bool × Bool) : Term :=
  .tuple #[Rustler.encodeBool value.1, Rustler.encodeBool value.2.1,
    Rustler.encodeBool value.2.2.1, Rustler.encodeBool value.2.2.2]

theorem facade (value : Bool) : __FACADE__ value = ownership_app.try_rw_cycle value := rfl

set_option maxHeartbeats 1000000 in
theorem adapter_next {β : Type} (value : Bool) (next : Term → Result β)
    (schedule : List ScheduleChoice) :
    (do let result ← Rustler.executeNative (__FACADE__ value) encode
        next result).run {} schedule =
      (next (encode (false, false, true, !value))).run {nativeRefCounter := 5} schedule := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [facade, Rustler.executeNative, Result.handle, Result.bind, ownership_app.try_rw_cycle,
      ownership_base.try_rw_toggle, ownership_base.try_rw_read, ownership_base.toggle,
      NativeRwLock.new, NativeRwLock.read, NativeRwLock.write, NativeRwLock.pollRead,
      NativeRwLock.pollWrite, NativeRwLock.prepareWrite, NativeRwLock.try_read,
      NativeRwLock.try_write, NativeRwLock.tryAcquireRead, NativeRwLock.tryAcquireWrite,
      NativeRwLock.acquireRead, NativeRwLock.acquireWrite, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.store,
      NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
      NativeRwLock.lease, NativeRwLock.readerLimit, NativeRwLock.typeName,
      NativeRwLock.releaseRead, NativeRwLock.releaseWrite, NativeRwLock.dispose,
      NativeRwReadGuard.deref, NativeRwWriteGuard.deref_mut, NativePoisonError.into_inner,
      NativeDrop.drop, NativeCodec.encode, NativeCodec.decode, NativeCodec.typeName,
      NativeM.allocate, NativeM.removeCell, NativeM.ok, NativeM.lift,
      Result.wait_run, Result.ofExcept, Result.nativeModify_bind, Result.nativeModify_run,
      Result.nativeGet_bind, List.eraseDups_cons, List.eraseDups_nil]

end TryRw.Properties
