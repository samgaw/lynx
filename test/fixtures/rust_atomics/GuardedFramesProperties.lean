module
public import FrameRuntime.Properties
public section
open Aeneas Aeneas.Std Lynx atomic_analysis
namespace FrameRuntime.GuardedProperties

theorem parse_contract (mutex : NativeMutex ReceiveState) :
    parse_frame mutex = (do
      let acquired ← NativeMutex.lock mutex
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let (result, bytes) ← atomic_core.frames.take_frame guard.value.buffer.bytes
      let (status, consumed) ← match result with
        | .Ok none => NativeM.ok (0#u8, 0#u64)
        | .Ok (some frame) => NativeM.lift (2#u8, UScalar.cast .U64 (alloc.vec.Vec.len frame))
        | .Err error => NativeM.ok (error, 0#u64)
      let remaining ← NativeM.lift (UScalar.cast .U64 (alloc.vec.Vec.len bytes))
      NativeGuard.release {guard with value := ⟨⟨bytes⟩⟩}
      .ok (status, consumed, remaining)) := by
  simp [parse_frame, NativeGuard.deref_mut, NativeGuard.deref,
    NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]
  all_goals
    congr 1
    funext result
    rcases result with ⟨outcome, bytes⟩
    cases outcome with
    | Ok frame => cases frame <;> simp
    | Err error => simp

end FrameRuntime.GuardedProperties
