module
public import __PREFIX__.Extraction.Funs
public section
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace __PREFIX__.Properties
open __ANALYSIS__

@[expose] def bounds (budget : U16) (result : Option U16) : Prop :=
  match result with
  | none => True
  | some used => 0 < used.val ∧ used.val ≤ budget.val

private theorem subtract (left right : U16) (bound : right.val ≤ left.val) :
    ∃ result, left - right = RustM.ok result ∧ result.val = left.val - right.val := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.sub_bv_spec bound))
  exact ⟨result, returned, facts.1⟩

private theorem add (left right : U16) (bound : left.val + right.val ≤ UScalar.max .U16) :
    ∃ result, left + right = RustM.ok result ∧ result.val = left.val + right.val := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.add_bv_spec bound))
  exact ⟨result, returned, facts.1⟩

@[expose] noncomputable def nodes : __CORE__.Node → Nat :=
  __CORE__.Node.rec
    (motive_1 := fun _ => Nat)
    (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat)
    (motive_4 := fun _ _ => Nat)
    (fun _ => 1) (fun _ => 1) (fun _ count => 1 + count)
    (fun _ count => count) (fun _ _ _ count => count)
    0 (fun _ _ head tail => head + tail)

@[simp] theorem nodes_binary (payload : alloc.vec.Vec U8) : nodes (.Binary payload) = 1 := rfl
@[simp] theorem nodes_text (text : String) : nodes (.Text text) = 1 := rfl

theorem nodes_sequence (children : alloc.vec.Vec __CORE__.Node) :
    nodes (.Sequence children) = 1 + (children.val.map nodes).sum := by
  rcases children with ⟨⟨n, values, bound⟩⟩
  induction values with
  | nil => rfl
  | cons head tail ih =>
    simp only [nodes, alloc.vec.Vec.val, Slice.val,
      Data.ListN.ListN.toList, List.map_cons, List.sum_cons]
    have previous := ih (by omega)
    simp only [nodes, alloc.vec.Vec.val, Slice.val] at previous
    omega

theorem nodes_positive (node : __CORE__.Node) : 0 < nodes node := by
  cases node with
  | Binary _ => simp
  | Text _ => simp
  | Sequence children => rw [nodes_sequence]; omega

@[expose] def exactCount (total : Nat) (budget : U16) (result : Option U16) : Prop :=
  match result with
  | none => budget.val < total
  | some used => used.val = total ∧ total ≤ budget.val

theorem children_exact (iter : core.slice.iter.Iter __CORE__.Node) (budget used : U16)
    (cursor : iter.i ≤ iter.slice.val.length)
    (init : 0 < used.val ∧ used.val ≤ budget.val)
    (child : ∀ node lower, lower.val < budget.val →
      Aeneas.Std.WP.spec (__CORE__.count node lower) (exactCount (nodes node) lower)) :
    Aeneas.Std.WP.spec (__CORE__.count_loop iter budget used)
      (exactCount (used.val + ((iter.slice.val.drop iter.i).map nodes).sum) budget) := by
  let total := used.val + ((iter.slice.val.drop iter.i).map nodes).sum
  unfold __CORE__.count_loop
  refine loop.spec_decr_nat
    (fun state : core.slice.iter.Iter __CORE__.Node × U16 => state.1.slice.val.length - state.1.i)
    (fun state => state.1.i ≤ state.1.slice.val.length ∧ 0 < state.2.val ∧ state.2.val ≤ budget.val ∧
      state.2.val + ((state.1.slice.val.drop state.1.i).map nodes).sum = total)
    (exactCount total budget) _ _ ?_ ⟨cursor, init.1, init.2, rfl⟩
  rintro ⟨current, used⟩ ⟨within, positive, fits, conservation⟩
  dsimp only at within positive fits conservation
  by_cases inside : current.i < current.slice.val.length
  · have dropped : current.slice.val.drop current.i =
        current.slice.val[current.i] :: current.slice.val.drop (current.i + 1) :=
      List.drop_eq_getElem_cons inside
    rw [dropped, List.map_cons, List.sum_cons] at conservation
    simp only [List.map_drop] at conservation
    obtain ⟨remaining, subtracted, difference⟩ := subtract budget used fits
    have smaller : remaining.val < budget.val := by omega
    obtain ⟨result, counted, correct⟩ := triple_iff_exists_ok.mp
      (Aeneas.Std.WP.spec_to_mvcgen (child current.slice.val[current.i] remaining smaller))
    simp only [__CORE__.count_loop.body, core.slice.iter.IteratorSliceIter.next,
      Slice.len_val, inside, ↓reduceDIte, bind_ok]
    change Aeneas.Std.WP.spec (do
      let remaining ← budget - used
      let result ← __CORE__.count current.slice.val[current.i] remaining
      let cf ← lift (Lynx.Rust.Try.optionBranch result)
      match cf with
      | core.ops.control_flow.ControlFlow.Continue value => do
        let next ← used + value
        RustM.ok (ControlFlow.cont (({slice := current.slice, i := current.i + 1} : core.slice.iter.Iter __CORE__.Node), next))
      | core.ops.control_flow.ControlFlow.Break residual => do
        let result ← lift (Lynx.Rust.Try.optionFromResidual U16 residual)
        RustM.ok (ControlFlow.done result)) _
    rw [subtracted]
    simp only [bind_ok, counted]
    cases result with
    | none =>
      simp only [exactCount] at correct
      simp [Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual,
        lift, exactCount, Aeneas.Std.WP.spec_ok]
      omega
    | some value =>
      simp only [exactCount] at correct
      have childPositive := nodes_positive current.slice.val[current.i]
      obtain ⟨next, added, sum⟩ := add used value (by scalar_tac)
      simp [Lynx.Rust.Try.optionBranch, lift, added, Aeneas.Std.WP.spec_ok]
      omega
  · have last : current.i = current.slice.val.length := by omega
    simp [last] at conservation
    simp [__CORE__.count_loop.body, core.slice.iter.IteratorSliceIter.next,
      inside, exactCount, conservation, Aeneas.Std.WP.spec_ok]
    omega

private theorem exact_at_budget (n : Nat) :
    ∀ node (budget : U16), budget.val = n →
      Aeneas.Std.WP.spec (__CORE__.count node budget) (exactCount (nodes node) budget) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro node budget same
    by_cases zero : budget = 0#u16
    · simp [__CORE__.count.eq_def, zero, exactCount,
        nodes_positive node, Aeneas.Std.WP.spec_ok]
    have positive : 0 < budget.val := by
      have : budget.val ≠ 0 := by intro h; apply zero; scalar_tac
      omega
    rw [__CORE__.count.eq_def]
    simp only [zero, ↓reduceIte]
    cases node with
    | Binary payload => simp [exactCount, Aeneas.Std.WP.spec_ok]; omega
    | Text text => simp [exactCount, Aeneas.Std.WP.spec_ok]; omega
    | Sequence children =>
      simp only [SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, bind_ok]
      have proof := children_exact ⟨alloc.vec.Vec.deref children, 0⟩ budget 1#u16
        (by simp) (by simp; omega) (by
          intro node lower smaller
          exact ih lower.val (by omega) node lower rfl)
      simpa [nodes_sequence, alloc.vec.Vec.deref] using proof

theorem count_exact (node : __CORE__.Node) (budget : U16) :
    Aeneas.Std.WP.spec (__CORE__.count node budget) (exactCount (nodes node) budget) :=
  exact_at_budget budget.val node budget rfl

theorem inspect_exact (node : __CORE__.Node) (budget : U16) :
    Aeneas.Std.WP.spec (__ANALYSIS__.tree_nodes node budget) (exactCount (nodes node) budget) :=
  count_exact node budget

theorem count_total (node : __CORE__.Node) (budget : U16) :
    Aeneas.Std.WP.spec (__CORE__.count node budget) (bounds budget) := by
  apply Aeneas.Std.WP.spec_mono (count_exact node budget)
  intro result correct
  cases result with
  | none => trivial
  | some used => exact ⟨by rw [correct.1]; exact nodes_positive node, correct.1 ▸ correct.2⟩

theorem inspect_fits (node : __CORE__.Node) (budget : U16)
    (fits : nodes node ≤ budget.val) :
    ∃ used, __ANALYSIS__.tree_nodes node budget = RustM.ok (some used) ∧ used.val = nodes node := by
  obtain ⟨result, returned, correct⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (inspect_exact node budget))
  cases result with
  | none => simp only [exactCount] at correct; omega
  | some used => exact ⟨used, returned, correct.1⟩

theorem inspect_rejects (node : __CORE__.Node) (budget : U16)
    (insufficient : budget.val < nodes node) :
    __ANALYSIS__.tree_nodes node budget = RustM.ok none := by
  obtain ⟨result, returned, correct⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (inspect_exact node budget))
  cases result with
  | none => exact returned
  | some used => simp only [exactCount] at correct; omega

end __PREFIX__.Properties
