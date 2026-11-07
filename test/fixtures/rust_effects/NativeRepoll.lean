module
public import Macro.Properties
public section
open Aeneas Aeneas.Std Lynx effects_native Macro.Properties
namespace Macro.Completion

theorem completion (value amount : U64) (env : Environment) :
    ∃ changed updated,
      finish_resource ⟨2,3⟩ amount ⟨⟨0, false⟩⟩ (live env value 3 false) =
        (.ok (.Ready changed, ⟨⟨0, false⟩⟩), reclaimed env 4 true) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  simp only [finish_resource, initial_state, NativeM.ok, monadLift_self, Result.ok_bind]
  rw [first_pending_next]
  simp only [Result.ok_bind]
  obtain ⟨changed, updated, computed, arithmetic⟩ := resume_next value amount env true
    (fun (reply, future, context) => do
      let (reply, context, frame) ← Result.ok (reply, context, future.pointer)
      resource_suspending.closure.drop_owned frame
      Result.ok (reply, context))
  refine ⟨changed, updated, ?_, arithmetic⟩
  simpa [completed_drop] using computed

end Macro.Completion
