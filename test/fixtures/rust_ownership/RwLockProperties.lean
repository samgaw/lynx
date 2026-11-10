module
public import Rw.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx ownership_nif
namespace Rw.Properties

theorem toggle_base (value : Bool) :
    ownership_base.toggle value = NativeM.ok (!value) := by
  cases value <;> rfl

theorem toggle_app (value : Bool) :
    ownership_app.toggle value = NativeM.ok (!value) := by
  simp [ownership_app.toggle, toggle_base, NativeM.ok]

@[expose] def initial : Environment := {}

set_option maxHeartbeats 1000000 in
theorem shared_then_exclusive (value : Bool) (schedule : List ScheduleChoice) :
    (rw_probe value).run initial schedule =
      (.ok (!value), {initial with nativeRefCounter := 5}) := by
  cases value <;>
    simp (config := {maxSteps := 500000}) [Result.wait_run,rw_probe, toggle_app, initial, NativeRwLock.new, NativeRwLock.read, NativeRwLock.pollRead, NativeRwLock.pollWrite, NativeRwLock.prepareWrite,
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
