module
public import Aeneas
-- Internal dependency for the fixed-point admissibility proof only.
-- Extracted programs consume the public monotonicity theorem below.
import all Init.Internal.Order.Basic
public section
open Aeneas Aeneas.Std Lean.Order
namespace __LOOP_NAMESPACE__

private theorem loop_le {α : Type u} {β : Type v}
    (left right : α → RustM (ControlFlow α β)) (below : left ⊑ right) :
    loop left ⊑ loop right := by
  apply loop.fixpoint_induct left (fun g => ∀ x, g x ⊑ loop right x)
  · apply admissible_pi
    intro x
    apply admissible_apply (P := fun _ value => value ⊑ loop right x) x
    unfold admissible
    intro c hc all
    exact csup_le hc all
  · intro g ih x
    rw [loop.eq_1 right x]
    have next :
        (fun cf : ControlFlow α β => match cf with
          | .cont r => g r | .done r => RustM.ok r) ⊑
        (fun cf : ControlFlow α β => match cf with
          | .cont r => loop right r | .done r => RustM.ok r) := by
      intro cf
      cases cf with
      | cont r => exact ih r
      | done r => exact PartialOrder.rel_refl
    exact (Aeneas.Std.bind_mono
      (fun p : RustM (ControlFlow α β) × (ControlFlow α β → RustM β) => p.1)
      (fun p cf => p.2 cf)
      (by intro a b h; exact h.1)
      (by intro a b h; exact h.2))
      (left x, fun cf => match cf with | .cont r => g r | .done r => RustM.ok r)
      (right x, fun cf => match cf with | .cont r => loop right r | .done r => RustM.ok r)
      ⟨below x, next⟩

@[partial_fixpoint_monotone] theorem loop_monotone
    {α : Type u} {β : Type v} {γ : Type w} [Lean.Order.PartialOrder γ]
    (body : γ → α → RustM (ControlFlow α β)) (x : α)
    (h : monotone body) : monotone (fun g => loop (body g) x) := by
  intro a b below
  exact loop_le (body a) (body b) (h a b below) x
end __LOOP_NAMESPACE__
