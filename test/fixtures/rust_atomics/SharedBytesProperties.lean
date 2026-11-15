module
public import SharedBytes.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace SharedBytes.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem append_eq (output : alloc.vec.Vec U8) (input : Slice U8)
    (bound : output.val.length + input.val.length ≤ 262144) :
    atomic_core.append_bytes output input =
      NativeM.ok (alloc.vec.Vec.from (output.val ++ input.val) (by scalar_tac)) := by
  rw [atomic_core.append_bytes, SharedBytes.Extraction.VectorModel.extend_bytes_eq, dite_eq_left bound]
  rfl

theorem payload_cleanup (value : atomic_core.BufferState) :
    atomic_core.BufferState.drop_owned value = NativeM.ok () := rfl

theorem cleanup_contract (value : SharedBuffer) :
    SharedBuffer.drop_owned value =
      NativeMutex.disposeWith atomic_core.BufferState.drop_owned value.state := rfl

theorem cleanup_run (mutex : NativeMutex atomic_core.BufferState)
    (value : atomic_core.BufferState) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName atomic_core.BufferState, .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (schedule : List ScheduleChoice) :
    (SharedBuffer.drop_owned ⟨mutex⟩).run env schedule =
      (.ok (), {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != mutex.id)}) := by
  cases poisoned <;>
    simp [cleanup_contract, NativeMutex.disposeWith, NativeMutex.into_inner, NativeMutex.intoInnerStep,
      stored, NativeCodec.roundtrip, payload_cleanup, NativeM.ok, Result.wait_run, Result.wait_bind]

theorem append_contract (mutex : NativeMutex atomic_core.BufferState) (input : Slice U8) :
    atomic_analysis.append_state mutex input = (do
      let acquired ← NativeMutex.lock mutex
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let bytes ← atomic_core.append_bytes guard.value.bytes input
      let length ← NativeM.lift (UScalar.cast .U64 (alloc.vec.Vec.len bytes))
      NativeGuard.release {guard with value := ⟨bytes⟩}
      .ok length) := by
  simp [atomic_analysis.append_state, NativeGuard.deref_mut, NativeGuard.deref,
    NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

@[expose] def state (value : atomic_core.BufferState) (poisoned : Bool) (env : Environment) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(1, NativeMutex.typeName atomic_core.BufferState,
    .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])]}

theorem append_run (value : atomic_core.BufferState) (input : Slice U8) (poisoned : Bool)
    (bound : value.bytes.val.length + input.val.length ≤ 262144) (env : Environment)
    (schedule : List ScheduleChoice) :
    (atomic_analysis.append_state ⟨1⟩ input).run (state value poisoned env) schedule =
      (.ok (U64.ofNatCore (value.bytes.val.length + input.val.length) (by scalar_tac)),
        {state ⟨alloc.vec.Vec.from (value.bytes.val ++ input.val) (by scalar_tac)⟩ poisoned env
          with nativeRefCounter := 2}) := by
  have appended := append_eq value.bytes input bound
  cases poisoned <;>
    simp [append_contract, state, NativeMutex.lock, NativeMutex.pollLock,
      NativeCodec.roundtrip, appended, NativeGuard.release, NativeGuard.pollRelease,
      NativePoisonError.into_inner, NativeM.ok, NativeM.lift, NativeM.castUsizeU64_eq,
      alloc.vec.Vec.len, Result.wait_run, Result.wait_bind]

theorem head_eq (bytes : Slice U8) :
    atomic_core.buffer_head bytes = NativeM.ok (bytes.val.headD 0#u8) := by
  cases contents : bytes.val <;>
    simp [atomic_core.buffer_head, core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice,
      core.slice.index.Usize.get, NativeM.lift, NativeM.ok, contents]

theorem read_contract (mutex : NativeMutex atomic_core.BufferState) :
    atomic_analysis.read_state mutex = (do
      let acquired ← NativeMutex.lock mutex
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let length ← NativeM.lift (UScalar.cast .U64 (alloc.vec.Vec.len guard.value.bytes))
      let head ← atomic_core.buffer_head (alloc.vec.Vec.deref guard.value.bytes)
      NativeGuard.release guard
      .ok (length, head)) := by
  simp [atomic_analysis.read_state, NativeGuard.deref, NativeOwnedDrop.drop,
    NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

theorem read_run (value : atomic_core.BufferState) (poisoned : Bool)
    (bound : value.bytes.val.length ≤ 262144) (env : Environment)
    (schedule : List ScheduleChoice) :
    (atomic_analysis.read_state ⟨1⟩).run (state value poisoned env) schedule =
      (.ok (U64.ofNatCore value.bytes.val.length (by scalar_tac), value.bytes.val.headD 0#u8),
        {(state value poisoned env) with nativeRefCounter := 2}) := by
  cases poisoned <;>
    simp [read_contract, state, NativeMutex.lock, NativeMutex.pollLock,
      NativeCodec.roundtrip, head_eq, NativeGuard.release, NativeGuard.pollRelease,
      NativePoisonError.into_inner, NativeM.ok, NativeM.lift, NativeM.castUsizeU64_eq,
      alloc.vec.Vec.len, alloc.vec.Vec.deref, Result.wait_run, Result.wait_bind]

@[expose] def live (value : atomic_core.BufferState) (poisoned : Bool) (env : Environment) : Environment :=
  {env with nativeRefCounter := 3, nativeHeap := [
    (3, NativeResourceArc.handleType SharedBuffer, .nativeReference 2),
    (2, NativeResourceArc.typeName SharedBuffer, .tuple #[.integer 1, NativeCodec.encode (SharedBuffer.mk ⟨1⟩)]),
    (1, NativeMutex.typeName atomic_core.BufferState,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])]}

theorem final_release (value : atomic_core.BufferState) (poisoned : Bool) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous) :
    shared_release ⟨2, 3⟩ (live value poisoned env) =
      (.ok (), {env with nativeRefCounter := 3, nativeHeap := []}) := by
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨2, 3⟩ : NativeResourceArc SharedBuffer) (SharedBuffer.mk ⟨1⟩) NativeM.ok (live value poisoned env)
    {env with nativeRefCounter := 3, nativeHeap := []}
    (.inr (by simpa [live] using policy))
    (by simp [live]) (by simp [live])
    (by simp [live, NativeResourceArc.handleType, NativeResourceArc.typeName])
    (by
      intro next
      cases poisoned <;>
        simp [NativeResourceCleanup.cleanup, cleanup_contract, NativeMutex.disposeWith,
          NativeMutex.into_inner, NativeMutex.intoInnerStep, NativeResourceArc.retiredState,
          live, NativeCodec.roundtrip, payload_cleanup, NativeM.ok, Result.wait_bind, Result.wait_run])
  have identity : (NativeResourceArc.releaseOwned (⟨2, 3⟩ : NativeResourceArc SharedBuffer) >>= NativeM.ok) =
      NativeResourceArc.releaseOwned (⟨2, 3⟩ : NativeResourceArc SharedBuffer) := Result.bind_ok _
  rw [identity] at released
  simpa [shared_release, monadLift_self, NativeOwnedDrop.drop, NativeM.ok] using released
end SharedBytes.Properties
