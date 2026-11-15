module
public import LockedBytes.Extraction.Funs
public import LockedBytes.ModelTests
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace LockedBytes.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem append_eq (output : alloc.vec.Vec U8) (input : Slice U8)
    (bound : output.val.length + input.val.length ≤ 262144) :
    atomic_core.append_bytes output input =
      NativeM.ok (alloc.vec.Vec.from (output.val ++ input.val) (by scalar_tac)) := by
  rw [atomic_core.append_bytes, LockedBytes.Extraction.VectorModel.extend_bytes_eq,
    dite_eq_left bound]
  rfl

theorem take_run (mutex : NativeMutex (alloc.vec.Vec U8))
    (value : alloc.vec.Vec U8) (poisoned : Bool) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName (alloc.vec.Vec U8), .tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])])
    (schedule : List ScheduleChoice) :
    (atomic_core.take_bytes mutex).run env schedule =
      (.ok value, {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != mutex.id)}) := by
  cases poisoned <;>
    simp [atomic_core.take_bytes, NativeMutex.into_inner, NativeMutex.intoInnerStep, stored,
      NativeCodec.roundtrip, NativePoisonError.into_inner, NativeM.ok,
      Result.wait_bind, Result.wait_run]

theorem locked_contract (bytes : NativeMutex (alloc.vec.Vec U8)) (input : Slice U8) :
    atomic_analysis.locked_append bytes input = (do
      let acquired ← NativeMutex.lock bytes
      let guard := match acquired with
        | .Ok guard => guard
        | .Err error => NativePoisonError.into_inner error
      let updated ← atomic_core.append_bytes guard.value input
      NativeGuard.release {guard with value := updated}
      .ok (alloc.vec.Vec.len updated)) := by
  simp [atomic_analysis.locked_append, NativeGuard.deref_mut, NativeGuard.deref,
    NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

@[expose] def state (value : alloc.vec.Vec U8) (poisoned : Bool) (env : Environment) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(1, NativeMutex.typeName (alloc.vec.Vec U8),
    .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode value])]}

theorem locked_run (value : alloc.vec.Vec U8) (input : Slice U8) (poisoned : Bool)
    (bound : value.val.length + input.val.length ≤ 262144) (env : Environment)
    (schedule : List ScheduleChoice) :
    (atomic_analysis.locked_append ⟨1⟩ input).run (state value poisoned env) schedule =
      (.ok (alloc.vec.Vec.len (alloc.vec.Vec.from (value.val ++ input.val) (by scalar_tac))),
        {(state (alloc.vec.Vec.from (value.val ++ input.val) (by scalar_tac)) poisoned env)
          with nativeRefCounter := 2}) := by
  have appended := append_eq value input bound
  cases poisoned <;>
    simp [locked_contract, state, NativeMutex.lock, NativeMutex.pollLock,
      NativeCodec.roundtrip, appended, NativeGuard.release, NativeGuard.pollRelease,
      NativePoisonError.into_inner, NativeM.ok, Result.wait_run, Result.wait_bind]

theorem copy_run (input : Slice U8) (bound : input.val.length ≤ 262144)
    (env : Environment) (empty : env.nativeHeap = []) (schedule : List ScheduleChoice) :
    (atomic_analysis.copy_locked input).run env schedule =
      (.ok (alloc.vec.Vec.from input.val (by scalar_tac)),
        {env with nativeRefCounter := env.nativeRefCounter + 2}) := by
  have appended := append_eq (alloc.vec.Vec.new U8) input (by simpa [alloc.vec.Vec.new] using bound)
  simp [atomic_analysis.copy_locked, locked_contract, atomic_core.take_bytes, appended,
    NativeMutex.new, NativeM.allocate, empty, NativeMutex.lock, NativeMutex.pollLock,
    NativeCodec.roundtrip, NativeMutex.into_inner, NativeMutex.intoInnerStep,
    NativeOwnedDrop.drop, NativeGuard.release, NativeGuard.pollRelease,
    NativePoisonError.into_inner, NativeM.ok, Result.wait_run, Result.wait_bind,
    alloc.vec.Vec.new, alloc.vec.Vec.len, alloc.vec.Vec.deref, Nat.add_assoc]
end LockedBytes.Properties
