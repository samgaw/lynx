module
public import __PREFIX__.Extraction.Funs
public section
open Aeneas Aeneas.Std
open Std.Do
namespace __PREFIX__.Properties

@[expose] def bounds (input : Slice U8) (nodes : U16) (result : Option __CORE__.Scan) : Prop :=
  match result with
  | none => True
  | some found => 0 < found.nodes.val ∧ found.nodes.val ≤ nodes.val ∧
      3 ≤ found.consumed.val ∧ found.consumed.val ≤ input.val.length

@[expose] def sequenceBounds (nodes : U16) (total : Usize) (result : Option __CORE__.Scan) : Prop :=
  match result with
  | none => True
  | some found => 0 < found.nodes.val ∧ found.nodes.val ≤ nodes.val ∧ found.consumed = total

private theorem subtract {ty} (left right : UScalar ty) (bound : right.val ≤ left.val) :
    ∃ result, left - right = RustM.ok result ∧ result.val = left.val - right.val := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.sub_bv_spec bound))
  exact ⟨result, returned, facts.1⟩

private theorem add {ty} (left right : UScalar ty) (bound : left.val + right.val ≤ UScalar.max ty) :
    ∃ result, left + right = RustM.ok result ∧ result.val = left.val + right.val := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.add_bv_spec bound))
  exact ⟨result, returned, facts.1⟩

theorem sequence_total (depth : U8) (nodes : U16) (total : Usize)
    (rest : Slice U8) (used : U16) (positive : 0 < depth.val)
    (init : 0 < used.val ∧ used.val ≤ nodes.val)
    (child : ∀ input lower budget, lower.val < depth.val →
      Aeneas.Std.WP.spec (__CORE__.scan input lower budget) (bounds input budget)) :
    Aeneas.Std.WP.spec (__CORE__.scan_loop depth nodes total rest used)
      (sequenceBounds nodes total) := by
  unfold __CORE__.scan_loop
  refine loop.spec_decr_nat (fun state : Slice U8 × U16 => state.1.val.length)
    (fun state => 0 < state.2.val ∧ state.2.val ≤ nodes.val)
    (sequenceBounds nodes total) _ _ ?_ init
  rintro ⟨rest, used⟩ ⟨positive_used, within⟩
  by_cases empty : rest.val = []
  · simp [__CORE__.scan_loop.body, core.slice.Slice.is_empty,
      Slice.length, empty, sequenceBounds, positive_used, within,
      Aeneas.Std.WP.spec_ok]
  · have nonempty : rest.val.length ≠ 0 := by simpa using empty
    obtain ⟨lower, lowered, lower_value⟩ := subtract depth 1#u8 (by simp; omega)
    obtain ⟨budget, budgeted, budget_value⟩ := subtract nodes used within
    have smaller : lower.val < depth.val := by simp at lower_value; omega
    obtain ⟨result, scanned, facts⟩ := triple_iff_exists_ok.mp (Aeneas.Std.WP.spec_to_mvcgen (child rest lower budget smaller))
    cases result with
    | none =>
      simp [__CORE__.scan_loop.body, core.slice.Slice.is_empty,
        Slice.length, nonempty, lowered, budgeted, scanned, lift,
        Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual,
        sequenceBounds, Aeneas.Std.WP.spec_ok]
    | some found =>
      simp only [bounds] at facts
      obtain ⟨nextUsed, added, next_value⟩ := add used found.nodes (by scalar_tac)
      let nextRest := rest.drop found.consumed
      have indexed : core.slice.Slice.get (core.slice.index.SliceIndexRangeFromUsizeSlice U8)
          rest { start := found.consumed } = RustM.ok (some nextRest) := by
        simp [core.slice.Slice.get, core.slice.index.SliceIndexRangeFromUsizeSlice.get,
          facts.2.2.2, nextRest]
      have decreasing : nextRest.val.length < rest.val.length := by
        simp only [nextRest, Slice.drop, Slice.from_val, List.length_drop]
        omega
      have kept : 0 < nextUsed.val ∧ nextUsed.val ≤ nodes.val := by
        rw [next_value]
        omega
      simp [__CORE__.scan_loop.body, core.slice.Slice.is_empty,
        Slice.length, nonempty, lowered, budgeted, scanned, added, indexed, lift,
        Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual,
        kept, decreasing, Aeneas.Std.WP.spec_ok]

private theorem scan_at_depth (n : Nat) :
    ∀ (input : Slice U8) (depth : U8) (nodes : U16), depth.val = n →
      Aeneas.Std.WP.spec (__CORE__.scan input depth nodes) (bounds input nodes) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro input depth nodes same
    by_cases zeroDepth : depth = 0#u8
    · simp [__CORE__.scan, zeroDepth, bounds, Aeneas.Std.WP.spec_ok]
    by_cases zeroNodes : nodes = 0#u16
    · simp [__CORE__.scan, zeroDepth, zeroNodes, bounds, Aeneas.Std.WP.spec_ok]
    by_cases short : input.val.length < 3
    · simp [__CORE__.scan, zeroDepth, zeroNodes, UScalar.lt_equiv,
        short, bounds, Aeneas.Std.WP.spec_ok]
    have index (i : Usize) (inside : i.val < input.val.length) :
        Slice.index_usize input i = RustM.ok input.val[i.val] := by
      simp [Slice.index_usize, inside]
    have indexed0 := index 0#usize (by simp; omega)
    have indexed1 := index 1#usize (by simp; omega)
    have indexed2 := index 2#usize (by simp; omega)
    let header := core.num.U16.from_be_bytes (Array.make 2#usize [input.val[1], input.val[2]])
    let payloadLen := UScalar.cast .Usize header
    have payloadBound : payloadLen.val ≤ 65535 := by
      dsimp only [payloadLen]
      rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
      · scalar_tac
      · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
    obtain ⟨total, added, totalValue⟩ := add payloadLen 3#usize (by scalar_tac)
    have totalLower : 3 ≤ total.val := by simp at totalValue; omega
    have positive : 0 < depth.val := by
      have : depth.val ≠ 0 := by intro eq; apply zeroDepth; scalar_tac
      omega
    have nodesPositive : 1 ≤ nodes.val := by
      have : nodes.val ≠ 0 := by intro eq; apply zeroNodes; scalar_tac
      omega
    rw [__CORE__.scan]
    simp only [zeroDepth, zeroNodes, UScalar.lt_equiv, Slice.len_val,
      ↓reduceIte, indexed0, indexed1, indexed2, bind_ok, lift]
    simp only [show (3#usize).val = 3 by simp, Slice.length, short, ↓reduceIte]
    simp only [show (0#usize).val = 0 by simp,
      show (1#usize).val = 1 by simp, show (2#usize).val = 2 by simp]
    rw [added]
    simp only [bind_ok]
    by_cases fits : total.val ≤ input.val.length
    · have start : 3#usize ≤ total := by simpa [UScalar.le_equiv] using totalLower
      simp only [core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
        start, fits, Slice.length, true_and, ↓reduceIte, bind_ok,
        Lynx.Rust.Try.optionBranch]
      split
      next tag0 => simp [bounds, totalLower, fits, nodesPositive, Aeneas.Std.WP.spec_ok]
      next tag1 =>
        apply Aeneas.Std.WP.spec_mono (sequence_total depth nodes total _ 1#u16 positive
          (by simpa using nodesPositive) (by
            intro child lower budget smaller
            exact ih lower.val (by omega) child lower budget rfl))
        intro result facts
        cases result with
        | none => trivial
        | some found =>
          simp only [sequenceBounds] at facts
          exact ⟨facts.1, facts.2.1, by rw [facts.2.2]; exact totalLower,
            by rw [facts.2.2]; exact fits⟩
      next tag2 =>
        obtain ⟨result, computed⟩ := __PREFIX__.Extraction.Bytes.fromUtf8_total _
        rw [computed]
        simp only [bind_ok]
        cases result <;> simp [bounds, nodesPositive, totalLower, fits, Aeneas.Std.WP.spec_ok]
      next other => simp [bounds, Aeneas.Std.WP.spec_ok]
    · simp [core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
        fits, Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual,
        bounds, Aeneas.Std.WP.spec_ok]

theorem scan_total (input : Slice U8) (depth : U8) (nodes : U16) :
    Aeneas.Std.WP.spec (__CORE__.scan input depth nodes) (bounds input nodes) :=
  scan_at_depth depth.val input depth nodes rfl


/-- The exact-document caller composes parser totality and node bounds. -/
theorem document_total (input : Slice U8) (depth : U8) (nodes : U16) :
    ∃ result, __ANALYSIS__.document_nodes input depth nodes = RustM.ok result ∧
      (∀ count, result = some count → 0 < count.val ∧ count.val ≤ nodes.val) := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (scan_total input depth nodes))
  cases result with
  | none =>
    simp [__ANALYSIS__.document_nodes, returned, lift,
      Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual]
  | some found =>
    simp only [bounds] at facts
    by_cases exactLength : found.consumed = Slice.len input
    · refine ⟨some found.nodes, ?_, ?_⟩
      · simp [__ANALYSIS__.document_nodes, returned, lift,
          Lynx.Rust.Try.optionBranch, exactLength]
      · intro count equal
        cases equal
        exact ⟨facts.1, facts.2.1⟩
    · refine ⟨none, ?_, by simp⟩
      simp [__ANALYSIS__.document_nodes, returned, lift,
        Lynx.Rust.Try.optionBranch, exactLength]

end __PREFIX__.Properties
