module
public import Signed.Extraction.Funs
public import Signed.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Signed.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem adjusted (balance : atomic_core.Balance) (delta : I64) :
    ∃ changed updated, atomic_core.adjust balance delta = NativeM.ok (changed, updated) ∧
      (if changed then updated.value.val = balance.value.val + delta.val
       else updated = balance ∧ ¬ (I64.min ≤ balance.value.val + delta.val ∧
         balance.value.val + delta.val ≤ I64.max)) := by
  have arithmetic := Lynx.Rust.Scalar.checkedAddI64_spec balance.value delta
  cases checked : I64.checked_add balance.value delta with
  | none =>
    refine ⟨false, balance, ?_, ?_⟩
    · simp [atomic_core.adjust, NativeM.lift, NativeM.ok, checked]
    · simpa [checked] using arithmetic
  | some value =>
    refine ⟨true, ⟨value⟩, ?_, ?_⟩
    · simp [atomic_core.adjust, NativeM.lift, NativeM.ok, checked]
    · simp only [checked] at arithmetic
      exact arithmetic.2.2


/-- The actual critical section composes the first-party checked mutation. -/
theorem locked_contract (mutex : NativeMutex atomic_core.Balance) (delta : I64) :
    atomic_analysis.locked_adjust mutex delta = (do
      let acquired ← NativeMutex.lock mutex
      let guard := match acquired with
        | .Ok guard => guard
        | .Err error => NativePoisonError.into_inner error
      let (changed, updated) ← atomic_core.adjust guard.value delta
      NativeGuard.release {guard with value := updated}
      .ok (changed, updated.value)) := by
  simp [atomic_analysis.locked_adjust, NativeGuard.deref_mut, NativeGuard.deref,
    NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

/-- An exact computational contract, retaining every native effect in the caller. -/
theorem adjusted_eq (balance : atomic_core.Balance) (delta : I64) :
    atomic_core.adjust balance delta =
      if (-9223372036854775808 : Int) ≤ balance.value.val + delta.val ∧
          balance.value.val + delta.val ≤ 9223372036854775807 then
        NativeM.ok (true, ⟨⟨BitVec.ofInt 64 (balance.value.val + delta.val)⟩⟩)
      else NativeM.ok (false, balance) := by
  unfold atomic_core.adjust
  rw [Lynx.Rust.Scalar.checkedAddI64_eq]
  split <;> simp [NativeM.lift, NativeM.ok]

/-- Allocation, acquisition, mutation, release and owner destruction are retained. -/
theorem facade_contract (value delta : I64) :
    __NIF__ value delta = (do
      let balance ← NativeMutex.new (⟨value⟩ : atomic_core.Balance)
      let result ← atomic_analysis.locked_adjust balance delta
      NativeOwnedDrop.drop balance
      .ok result) := rfl

/-- Both directions of fixed-width signed state survive heap representation. -/
theorem signed_roundtrip {ty : IScalarTy} (value : IScalar ty) :
    NativeCodec.decode (NativeCodec.encode value) = some value := NativeCodec.roundtrip value

theorem facade_run (value delta : I64) (changed : Bool) (updated : atomic_core.Balance)
    (adjusted : atomic_core.adjust ⟨value⟩ delta = NativeM.ok (changed, updated))
    (env : Environment) (empty : env.nativeHeap = []) (schedule : List ScheduleChoice) :
    (__NIF__ value delta).run env schedule =
      (.ok (changed, updated.value), {env with nativeRefCounter := env.nativeRefCounter + 2}) := by
  simp [__NIF__, locked_contract,
    NativeMutex.new, NativeM.allocate, empty, NativeMutex.lock, NativeMutex.pollLock,
    NativeCodec.roundtrip, adjusted, NativeOwnedDrop.drop, NativeGuard.release,
    NativeGuard.pollRelease, NativeMutex.dispose, NativeM.readCell, NativeM.removeCell,
    NativeM.ok, Result.wait_run, Result.wait_bind,
    Nat.add_assoc]

/-- Signed and unsigned cells cannot share a nominal state schema. -/
theorem signed_unsigned_distinct :
    NativeCodec.typeName (α := I64) ≠ NativeCodec.typeName (α := U64) := by decide +kernel

/-- Heap decoding never wraps an out-of-range signed integer. -/
theorem signed_range_rejected (ty : IScalarTy) (value : Int)
    (outside : value < -(2 ^ (ty.numBits - 1) : Int) ∨ (2 ^ (ty.numBits - 1) : Int) ≤ value) :
    NativeCodec.decode (α := IScalar ty) (.integer value) = none :=
  NativeCodec.decode_signed_outOfRange ty value outside

end Signed.Properties
