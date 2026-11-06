module
public import Runtime.CriticalProperties
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.CriticalConcurrent

open Runtime.CriticalProperties

private abbrev Acquired := Except Exception
  (core.result.Result (NativeGuard effects_core.Counter) (NativePoisonError (NativeGuard effects_core.Counter)))

private def finish (reply : Except Exception Unit) : Result Term :=
  match reply with
  | .ok _ => .ok Term.true
  | .error error => .error error

private def postAcquire (amount : U64) (reply : Acquired) : Result Term :=
  match reply with
  | .error error => .error error
  | .ok acquired => do
    let guard ← effects_core.recover_guard acquired
    let (changed, updated) ← effects_core.increment guard.value amount
    NativeGuard.release { guard with value := updated }
    return if changed then Term.true else Term.false

private theorem worker_wait (amount : U64) :
    (do let changed ← locked_increment ⟨1⟩ amount
        return if changed then Term.true else Term.false : Result Term) =
      .wait (NativeMutex.pollLock ⟨1⟩) (postAcquire amount) := by
  rw [critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind, bind_assoc]
  congr 1
  funext reply
  cases reply <;> simp [postAcquire, NativeM.ok]

private theorem increment_expected (before amount after : U64)
    (sum : after.val = before.val + amount.val) :
    effects_core.increment ⟨before⟩ amount = Result.ok (true, ⟨after⟩) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec ⟨before⟩ amount
  cases changed with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at property
    have bound : after.val ≤ U64.max := by scalar_tac
    omega
  | true =>
    simp only [↓reduceIte] at property
    have equal : updated = effects_core.Counter.mk after := by
      cases updated with
      | mk value =>
        exact congrArg effects_core.Counter.mk (UScalar.eq_of_val_eq (property.trans sum.symm))
    simpa [equal] using returned

private def unlocked (value : U64) : Term :=
  .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk value)]

private def shared (counter : Nat) (contents : Term) : Nat × List (Nat × String × Term) :=
  (counter, [(1, NativeMutex.typeName effects_core.Counter, contents)])

/-- Two actual extracted critical sections preserve both writes under this
contending schedule. Native contexts here are modeled local Lynx processes. -/
theorem updates_interleave (before parentAmount childAmount intermediate final : U64)
    (parentSum : intermediate.val = before.val + parentAmount.val)
    (childSum : final.val = intermediate.val + childAmount.val) :
    let worker := fun amount : U64 => (do
      let changed ← locked_increment ⟨1⟩ amount
      return if changed then Term.true else Term.false : Result Term)
    let computation : Result Term := do
      let _ ← Result.schedule (worker childAmount) .ok
      worker parentAmount
    let observed := computation {
      refCounter := 1
      nativeHeap := [(1, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk before)])]
      schedule := [.current, .swap 2]
    }
    observed.1 = .ok Term.true ∧ observed.2.nativeHeap =
      [(1, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk final)])] := by
  have trace := Result.two_wait_interleave
    (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (postAcquire parentAmount)
    (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (postAcquire childAmount)
    (NativeGuard.pollRelease (⟨⟨1⟩, 2, 1, ⟨intermediate⟩⟩ : NativeGuard effects_core.Counter)) finish
    (NativeGuard.pollRelease (⟨⟨1⟩, 3, 2, ⟨final⟩⟩ : NativeGuard effects_core.Counter)) finish
    (.ok (.Ok ⟨⟨1⟩, 2, 1, ⟨before⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨intermediate⟩⟩))
    (.ok ()) (.ok ()) Term.true Term.true
    (shared 1 (unlocked before))
    (shared 2 (NativeMutex.lockedContents 1 2 false (effects_core.Counter.mk before)))
    (shared 2 (unlocked intermediate))
    (shared 3 (NativeMutex.lockedContents 2 3 false (effects_core.Counter.mk intermediate)))
    (shared 3 (unlocked final))
    (by simp [shared, unlocked, NativeMutex.pollLock, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by
      have updated := increment_expected before parentAmount intermediate parentSum
      simp [postAcquire, effects_core.recover_guard, NativeM.ok, updated,
        NativeGuard.release, Result.wait_bind]
      funext reply
      cases reply <;> simp [finish])
    (by simp [shared, NativeMutex.pollLock, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by simp [shared, unlocked, NativeGuard.pollRelease, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by rfl)
    (by simp [shared, unlocked, NativeMutex.pollLock, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by
      have updated := increment_expected intermediate childAmount final childSum
      simp [postAcquire, effects_core.recover_guard, NativeM.ok, updated,
        NativeGuard.release, Result.wait_bind]
      funext reply
      cases reply <;> simp [finish])
    (by simp [shared, unlocked, NativeGuard.pollRelease, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by rfl)
  dsimp only
  simp only [worker_wait, Result.schedule_bind, Result.ok_bind]
  have computed := trace
  simp only [shared, unlocked] at computed
  rw [computed]
  constructor <;> rfl

/-- Two actual extracted critical sections preserve both writes under this
contending schedule. Native contexts here are modeled local Lynx processes. -/
theorem updates_interleave_child_first (before parentAmount childAmount intermediate final : U64)
    (childSum : intermediate.val = before.val + childAmount.val)
    (parentSum : final.val = intermediate.val + parentAmount.val) :
    let worker := fun amount : U64 => (do
      let changed ← locked_increment ⟨1⟩ amount
      return if changed then Term.true else Term.false : Result Term)
    let computation : Result Term := do
      let _ ← Result.schedule (worker childAmount) .ok
      worker parentAmount
    let observed := computation {
      refCounter := 1
      nativeHeap := [(1, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk before)])]
      schedule := [.swap 2, .swap 1]
    }
    observed.1 = .ok Term.true ∧ observed.2.nativeHeap =
      [(1, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk final)])] := by
  have trace := Result.two_wait_interleave_child_first
    (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (postAcquire parentAmount)
    (NativeMutex.pollLock (α := effects_core.Counter) ⟨1⟩) (postAcquire childAmount)
    (NativeGuard.pollRelease (⟨⟨1⟩, 3, 1, ⟨final⟩⟩ : NativeGuard effects_core.Counter)) finish
    (NativeGuard.pollRelease (⟨⟨1⟩, 2, 2, ⟨intermediate⟩⟩ : NativeGuard effects_core.Counter)) finish
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨intermediate⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 2, 2, ⟨before⟩⟩))
    (.ok ()) (.ok ()) Term.true Term.true
    (shared 1 (unlocked before))
    (shared 2 (NativeMutex.lockedContents 2 2 false (effects_core.Counter.mk before)))
    (shared 2 (unlocked intermediate))
    (shared 3 (NativeMutex.lockedContents 1 3 false (effects_core.Counter.mk intermediate)))
    (shared 3 (unlocked final))
    (by simp [shared, unlocked, NativeMutex.pollLock, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by
      have updated := increment_expected before childAmount intermediate childSum
      simp [postAcquire, effects_core.recover_guard, NativeM.ok, updated,
        NativeGuard.release, Result.wait_bind]
      funext reply
      cases reply <;> simp [finish])
    (by simp [shared, NativeMutex.pollLock, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by simp [shared, unlocked, NativeGuard.pollRelease, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by rfl)
    (by simp [shared, unlocked, NativeMutex.pollLock, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by
      have updated := increment_expected intermediate parentAmount final parentSum
      simp [postAcquire, effects_core.recover_guard, NativeM.ok, updated,
        NativeGuard.release, Result.wait_bind]
      funext reply
      cases reply <;> simp [finish])
    (by simp [shared, unlocked, NativeGuard.pollRelease, NativeCodec.roundtrip, NativeMutex.lockedContents])
    (by rfl)
  dsimp only
  simp only [worker_wait, Result.schedule_bind, Result.ok_bind]
  have computed := trace
  simp only [shared, unlocked] at computed
  rw [computed]
  constructor <;> rfl

end Runtime.CriticalConcurrent
