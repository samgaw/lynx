module
public import EffectCalls.Core
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace EffectCalls.Properties

/-- Identical constructor inputs produce two distinct identities and cells. -/
theorem distinct_allocations (value : U64) :
    identical_mutexes value {} = (.ok (⟨1⟩, ⟨2⟩), {
      refCounter := 2, nativeHeap := [
        (2, NativeMutex.typeName U64,
          .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value]),
        (1, NativeMutex.typeName U64,
          .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])] }) := by
  simp [identical_mutexes, NativeMutex.new, NativeM.allocate, NativeM.ok]

/-- An unused return value does not erase the actual first-party critical section. -/
theorem discarded_effect (mutex : NativeMutex effects_core.Counter) (amount : U64) :
    discarded_update mutex amount = (do
      let _ ← effects_core.locked_increment mutex amount
      effects_core.locked_increment mutex amount) := by rfl

@[expose] def state (value : U64) (counter : Nat) : Environment :=
  {refCounter := counter, nativeHeap := [
    (1, NativeMutex.typeName effects_core.Counter,
      .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk value)])]}

private theorem one_next {α : Type} (before after amount : U64) (counter : Nat)
    (next : Bool → NativeM α) (fresh : counter + 1 ≠ 1)
    (sum : after.val = before.val + amount.val) :
    (effects_core.locked_increment ⟨1⟩ amount >>= next) (state before counter) =
      next true (state after (counter + 1)) := by
  obtain ⟨changed, updated, observed, arithmetic⟩ :=
    EffectCalls.Core.critical_state_next next
      ⟨1⟩ ⟨before⟩ amount false (state before counter)
      (by simp [state]) (by simp [state]; omega)
  have selected : changed = true := by
    cases changed <;> simp_all
    have bound : after.val ≤ U64.max := by scalar_tac
    omega
  subst changed
  simp only [↓reduceIte] at arithmetic
  have same : updated = effects_core.Counter.mk after := by
    cases updated with
    | mk value => exact congrArg effects_core.Counter.mk (UScalar.eq_of_val_eq (arithmetic.trans sum.symm))
  simpa [Result.handle, Result.bind_ok, same, state] using observed

/-- The unused first result still updates the shared value; the next call sees it. -/
theorem discarded_state :
    discarded_update ⟨1⟩ 1#u64 (state 0#u64 1) = (.ok true, state 2#u64 3) := by
  simp only [discarded_update, monadLift_self]
  rw [one_next 0#u64 1#u64 1#u64 1 _ (by decide) (by decide)]
  have final := one_next 1#u64 2#u64 1#u64 2 Result.ok (by decide) (by decide)
  simpa [Result.bind_ok, Result.ok_apply] using final

end EffectCalls.Properties
