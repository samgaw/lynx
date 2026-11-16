module
public import CapturedShared.CapturedProperties
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace CapturedShared.NifProperties

theorem frame_contract (owner : NativeResourceArc SharedBuffer) (accepted : Bool) :
    __FRAME__ owner accepted = (do
      let value ← NativeResourceArc.deref owner
      let acquired ← NativeMutex.lock value.state
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let result ← atomic_analysis.guard_frame guard accepted
      NativeResourceArc.releaseOwned owner
      NativeM.ok result) := by
  simp [__FRAME__, NativeOwnedDrop.drop, NativeResourceUnwindDrop.drop, NativeM.ok]
  congr 1
  funext value
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]
  all_goals
    congr 1
    funext result
    cases result <;> simp

theorem payload_cleanup (value : SharedBuffer) :
    SharedBuffer.drop_owned value = NativeMutex.disposeWith (fun _ => NativeM.ok ()) value.state := by
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem new_unregistered (env : Environment) (schedule : List ScheduleChoice) :
    (__NEW__).run
      {env with nativeHeap := [], nativeResourceTypes := []} schedule =
      (.ok (.Err ()), {env with nativeHeap := [], nativeResourceTypes := [], nativeRefCounter := env.nativeRefCounter + 1}) := by
  simp [__NEW__,
    NativeResourceArc.newManagedCaptured, NativeResourceArc.newOwned,
    NativeResourceCleanup.cleanup, SharedBuffer.drop_owned, NativeOwnedDrop.drop,
    NativeMutexDrop.drop, NativeMutex.disposeWith, NativeMutex.into_inner,
    NativeMutex.intoInnerStep, NativeMutex.new, NativeM.allocate,
    NativeM.capturePanic, NativeM.fail, NativeM.ok, NativeM.lift,
    atomic_analysis.ReceiveState.drop_owned, NativeCodec.roundtrip,
    Result.wait_run, Result.handle, alloc.vec.Vec.new]

end CapturedShared.NifProperties
