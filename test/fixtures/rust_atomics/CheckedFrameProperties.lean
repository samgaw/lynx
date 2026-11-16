module
public import FrameRuntime.Properties
public section
open Aeneas Aeneas.Std Lynx atomic_analysis
namespace FrameRuntime.CheckedProperties
theorem checked_contract (input : alloc.vec.Vec U8) (accepted : Bool) :
    checked_frame input accepted = (do
      let (reply, bytes) ← atomic_core.frames.take_frame input
      NativeM.ok ((if accepted then .Ok reply else .Err ()), bytes)) := by
  cases accepted <;> simp [checked_frame, atomic_core.accept_frame, NativeM.ok]

theorem checked_consumes_exact (input : alloc.vec.Vec U8) (accepted : Bool)
    (high low : U8) (payload tail : List U8)
    (shape : input.val = [1#u8, high, low] ++ payload ++ tail)
    (wire : (core.num.U16.from_be_bytes (Array.make 2#usize [high, low])).val = payload.length)
    (bound : input.val.length ≤ 262144) :
    ∃ frame rest, checked_frame input accepted =
        NativeM.ok ((if accepted then .Ok (.Ok (some frame)) else .Err ()), rest) ∧
      frame.val = [1#u8, high, low] ++ payload ∧ rest.val = tail := by
  obtain ⟨frame, rest, parsed, frame_bytes, remaining⟩ :=
    FrameRuntime.Properties.consumes_exact input high low payload tail shape wire bound
  refine ⟨frame, rest, ?_, frame_bytes, remaining⟩
  rw [checked_contract, parsed]
  simp [NativeM.ok]

end FrameRuntime.CheckedProperties
