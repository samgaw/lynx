module
public import Runtime.Guard.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.GuardProperties

/-- The extracted cross-crate callee computes the sum or preserves the counter. -/
theorem increment_spec (counter : effects_core.Counter) (amount : U64) :
    ∃ success updated, effects_core.increment counter amount = Result.ok (success, updated) ∧
      (if success then updated.value.val = counter.value.val + amount.val
       else updated = counter ∧ U64.max < counter.value.val + amount.val) := by
  have arithmetic := U64.checked_add_bv_spec counter.value amount
  cases checked : U64.checked_add counter.value amount with
  | none =>
    refine ⟨false, counter, ?_, ?_⟩
    · simp [effects_core.increment, NativeM.lift, NativeM.ok, checked]
    · simpa [checked] using arithmetic
  | some value =>
    refine ⟨true, ⟨value⟩, ?_, ?_⟩
    · simp [effects_core.increment, NativeM.lift, NativeM.ok, checked]
    · have found := arithmetic
      simp only [checked] at found
      exact found.2.1


/-- The actual guard callee uses the checked first-party transition and retains
its reconstructed borrow. No acquisition or release is asserted here. -/
theorem callee_contract (guard : NativeGuard effects_core.Counter) (amount : U64) :
    effects_core.increment_guard guard amount = (do
      let (changed, updated) ← effects_core.increment guard.value amount
      .ok (changed, { guard with value := updated })) := by
  simp [effects_core.increment_guard, NativeGuard.deref_mut, NativeM.lift, NativeM.ok]

/-- A caller in another crate composes the proved callee contract. -/
theorem composed_update (guard : NativeGuard effects_core.Counter) (amount : U64) :
    guard_increment guard amount = (do
      let (changed, updated) ← effects_core.increment guard.value amount
      .ok (changed, { guard with value := updated })) := by
  change effects_core.increment_guard guard amount = _
  exact callee_contract guard amount

/-- A shared borrow observes the current payload view. -/
theorem read_payload (guard : NativeGuard effects_core.Counter) :
    guard_read guard = Result.ok guard.value.value := by
  simp [guard_read, effects_core.read_guard, NativeGuard.deref, NativeM.ok]

/-- Updates compute the sum, reject overflow without changing the payload, and
preserve the guard's mutex, acquisition token and owning context. -/
theorem update_spec (guard : NativeGuard effects_core.Counter) (amount : U64) :
    ∃ changed updated,
      guard_increment guard amount = Result.ok (changed, { guard with value := updated }) ∧
      (if changed then updated.value.val = guard.value.value.val + amount.val
       else updated = guard.value ∧ U64.max < guard.value.value.val + amount.val) := by
  obtain ⟨changed, updated, returned, property⟩ := increment_spec guard.value amount
  refine ⟨changed, updated, ?_, property⟩
  simp [composed_update, returned, NativeM.ok]

/-- Borrowing alone does not change the shared heap, mailbox or scheduler. The
updated payload is returned in the guard; committing it requires release. -/
theorem update_environment (guard : NativeGuard effects_core.Counter) (amount : U64)
    (env : Environment) :
    ∃ changed updated, guard_increment guard amount env =
      (.ok (changed, { guard with value := updated }), env) := by
  obtain ⟨changed, updated, returned, _⟩ := update_spec guard amount
  exact ⟨changed, updated, by simp [returned]⟩

end Runtime.GuardProperties
