module
public import SharedFrames.ParserProperties
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace SharedFrames.NifProperties

theorem parse_contract (mutex : NativeMutex atomic_analysis.ReceiveState) :
    atomic_analysis.parse_frame mutex = (do
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
  simp [atomic_analysis.parse_frame, NativeGuard.deref_mut, NativeGuard.deref,
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

theorem frame_contract (owner : NativeResourceArc SharedBuffer) :
    __FRAME__ owner = (do
      let value ← NativeResourceArc.deref owner
      let result ← atomic_analysis.parse_frame value.state
      NativeResourceArc.releaseOwned owner
      .ok result) := by
  simp [__FRAME__, NativeOwnedDrop.drop, NativeM.ok]

@[expose] def state (value : atomic_analysis.ReceiveState) (poisoned : Bool)
    (env : Environment) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(1, NativeMutex.typeName atomic_analysis.ReceiveState,
    .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])]}

theorem short_run (value : atomic_analysis.ReceiveState) (poisoned : Bool)
    (bound : value.buffer.bytes.val.length < 3) (env : Environment)
    (schedule : List ScheduleChoice) :
    (atomic_analysis.parse_frame ⟨1⟩).run (state value poisoned env) schedule =
      (.ok (0#u8, 0#u64, U64.ofNatCore value.buffer.bytes.val.length (by have limit := value.buffer.bytes.property; cases System.Platform.numBits_eq <;> simp_all [Usize.numBits, UScalarTy.numBits, Usize.max] <;> omega)),
        {state value poisoned env with nativeRefCounter := 2}) := by
  have parsed := SharedFrames.ParserProperties.short value.buffer.bytes bound
  cases poisoned <;>
    simp [parse_contract, state, NativeMutex.lock, NativeMutex.pollLock,
      NativeCodec.roundtrip, parsed, NativeGuard.release, NativeGuard.pollRelease,
      NativePoisonError.into_inner, NativeM.ok, NativeM.lift, NativeM.castUsizeU64_eq,
      alloc.vec.Vec.len, Result.wait_run, Result.wait_bind]

theorem wrong_version_run (value : atomic_analysis.ReceiveState) (poisoned : Bool)
    (version high low : U8) (rest : List U8)
    (shape : value.buffer.bytes.val = [version, high, low] ++ rest)
    (wrong : version ≠ 1#u8) (env : Environment) (schedule : List ScheduleChoice) :
    (atomic_analysis.parse_frame ⟨1⟩).run (state value poisoned env) schedule =
      (.ok (1#u8, 0#u64, U64.ofNatCore value.buffer.bytes.val.length (by have limit := value.buffer.bytes.property; cases System.Platform.numBits_eq <;> simp_all [Usize.numBits, UScalarTy.numBits, Usize.max] <;> omega)),
        {state value poisoned env with nativeRefCounter := 2}) := by
  have parsed := SharedFrames.ParserProperties.wrong_version value.buffer.bytes version high low rest shape wrong
  cases poisoned <;>
    simp [parse_contract, state, NativeMutex.lock, NativeMutex.pollLock,
      NativeCodec.roundtrip, parsed, NativeGuard.release, NativeGuard.pollRelease,
      NativePoisonError.into_inner, NativeM.ok, NativeM.lift, NativeM.castUsizeU64_eq,
      alloc.vec.Vec.len, Result.wait_run, Result.wait_bind]

end SharedFrames.NifProperties
