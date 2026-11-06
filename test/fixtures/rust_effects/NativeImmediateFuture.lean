module
public import Future.Extraction.Funs
public section
open Aeneas Aeneas.Std effects_native
namespace Future.Properties

theorem core_increment (value : U64) :
    ∃ result, effects_core.saturating_increment value = RustM.ok result ∧
      result.val = min U64.max (value.val + 1) := by
  refine ⟨core.num.U64.saturating_add value 1#u64, rfl, ?_⟩
  simp

theorem initial_state (value : U64) :
    immediate_increment value = RustM.ok ⟨value, 0#u32⟩ := rfl

/-- The actual compiler poll body calls the actual first-party computation. -/
theorem first_poll (value : U64) :
    ∃ result future,
      (do
        let initial ← immediate_increment value
        immediate_increment.closure.poll ⟨initial⟩ ()) =
          RustM.ok (core.task.poll.Poll.Ready result, future, ()) ∧
      result.val = min U64.max (value.val + 1) ∧
      future.pointer.state = 1#u32 := by
  obtain ⟨result, computed, arithmetic⟩ := core_increment value
  refine ⟨result, ⟨⟨value, 1#u32⟩⟩, ?_, arithmetic, rfl⟩
  simp [immediate_increment, immediate_increment.closure.poll, computed]; rfl

/-- Completion is retained; polling again follows the compiler's panic branch. -/
theorem repoll_completed (value : U64) :
    immediate_increment.closure.poll ⟨⟨value, 1#u32⟩⟩ () = RustM.fail .panic := by
  rfl

end Future.Properties
