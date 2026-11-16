module
public import FrameRuntime.CheckedProperties
public section
open Aeneas Aeneas.Std Lynx atomic_analysis
namespace FrameRuntime.CapturedProperties
open FrameRuntime.CheckedProperties
abbrev Reply := core.result.Result (Option (alloc.vec.Vec U8)) U8
abbrev CapturedReply := core.result.Result Reply Unit

theorem guard_contract (guard : NativeGuard ReceiveState) (accepted : Bool) :
    guard_frame guard accepted = (do
      let (reply, bytes) ← atomic_core.frames.take_frame guard.value.buffer.bytes
      let updated := {guard with value := ⟨⟨bytes⟩⟩}
      if accepted then
        NativeGuard.release updated
        NativeM.ok (.Ok reply)
      else
        NativeGuard.releasePanicking updated
        NativeM.ok (.Err ())) := by
  cases accepted <;>
    simp [guard_frame, checked_contract, NativeGuard.deref_mut, NativeM.lift,
      NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop]

theorem guard_consumes_exact (guard : NativeGuard ReceiveState) (accepted : Bool)
    (high low : U8) (payload tail : List U8)
    (shape : guard.value.buffer.bytes.val = [1#u8, high, low] ++ payload ++ tail)
    (wire : (core.num.U16.from_be_bytes (Array.make 2#usize [high, low])).val = payload.length)
    (bound : guard.value.buffer.bytes.val.length ≤ 262144) :
    ∃ frame rest, guard_frame guard accepted = (do
        let updated := {guard with value := ⟨⟨rest⟩⟩}
        if accepted then
          NativeGuard.release updated
          NativeM.ok (.Ok (.Ok (some frame)))
        else
          NativeGuard.releasePanicking updated
          NativeM.ok (.Err ())) ∧
      frame.val = [1#u8, high, low] ++ payload ∧ rest.val = tail := by
  obtain ⟨frame, rest, parsed, frame_bytes, remaining⟩ :=
    FrameRuntime.Properties.consumes_exact guard.value.buffer.bytes high low payload tail
      shape wire bound
  refine ⟨frame, rest, ?_, frame_bytes, remaining⟩
  rw [guard_contract, parsed]
  simp [NativeM.ok]

theorem guard_heap (guard : NativeGuard ReceiveState) (accepted poisoned : Bool)
    (reply : Reply) (bytes : alloc.vec.Vec U8) (original : ReceiveState)
    (parsed : atomic_core.frames.take_frame guard.value.buffer.bytes = NativeM.ok (reply, bytes))
    (env : Environment) (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName ReceiveState,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    guard_frame guard accepted env =
      (.ok (if accepted then .Ok reply else .Err ()),
       {env with nativeHeap := env.nativeHeap.map fun cell =>
         if cell.1 == guard.mutex.id then
           (guard.mutex.id, NativeMutex.typeName ReceiveState,
            .tuple #[.atom "unlocked", .atom (if poisoned || !accepted then "poisoned" else "unpoisoned"),
              NativeCodec.encode (ReceiveState.mk (atomic_core.BufferState.mk bytes))])
         else cell}) := by
  rw [guard_contract, parsed]
  cases accepted
  · simpa [NativeM.ok] using
      (NativeGuard.releasePanicking_owned_next {guard with value := ⟨⟨bytes⟩⟩}
        original poisoned (NativeM.ok (.Err ()) : NativeM CapturedReply) env owner stored)
  · simpa [NativeM.ok] using
      (NativeGuard.release_owned_next {guard with value := ⟨⟨bytes⟩⟩}
        original poisoned (NativeM.ok (.Ok reply) : NativeM CapturedReply) env owner stored)
end FrameRuntime.CapturedProperties
