module
public import __PREFIX__.Properties
public section
open Aeneas Aeneas.Std
namespace __PREFIX__.Cases
@[expose] def packet : Slice U8 := Slice.from
  [1#u8,0#u8,8#u8,0#u8,0#u8,0#u8,2#u8,0#u8,2#u8,195#u8,169#u8] (by scalar_tac)
private theorem add_exact {ty} (a b c : UScalar ty)
    (safe : a.val + b.val ≤ UScalar.max ty) (value : c.val = a.val + b.val) :
    a + b = RustM.ok c := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.add_bv_spec safe))
  have equal : result = c := by apply UScalar.eq_of_val_eq; omega
  simpa only [equal] using returned

private theorem sub_exact {ty} (a b c : UScalar ty)
    (safe : b.val ≤ a.val) (value : c.val = a.val - b.val) :
    a - b = RustM.ok c := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.sub_bv_spec safe))
  have equal : result = c := by apply UScalar.eq_of_val_eq; omega
  simpa only [equal] using returned

theorem siblings : __CORE__.scan packet 2#u8 3#u16 =
    RustM.ok (some ⟨3#u16, 11#usize⟩) := by
  have h8 : core.num.U16.from_be_bytes (Array.make 2#usize [0#u8,8#u8]) = 8#u16 := by decide +kernel
  have h2 : core.num.U16.from_be_bytes (Array.make 2#usize [0#u8,2#u8]) = 2#u16 := by decide +kernel
  have h0 : core.num.U16.from_be_bytes (Array.make 2#usize [0#u8,0#u8]) = 0#u16 := by decide +kernel
  have cast8 : UScalar.cast .Usize 8#u16 = 8#usize := by scalar_tac
  have cast2 : UScalar.cast .Usize 2#u16 = 2#usize := by scalar_tac
  have cast0 : UScalar.cast .Usize 0#u16 = 0#usize := by scalar_tac
  have add8 := add_exact 8#usize 3#usize 11#usize (by scalar_tac) (by simp)
  have add2 := add_exact 2#usize 3#usize 5#usize (by scalar_tac) (by simp)
  have add0 := add_exact 0#usize 3#usize 3#usize (by scalar_tac) (by simp)
  have add11 := add_exact 1#u16 1#u16 2#u16 (by scalar_tac) (by simp)
  have add21 := add_exact 2#u16 1#u16 3#u16 (by scalar_tac) (by simp)
  have subDepth := sub_exact 2#u8 1#u8 1#u8 (by simp) (by simp)
  have sub31 := sub_exact 3#u16 1#u16 2#u16 (by simp) (by simp)
  have sub32 := sub_exact 3#u16 2#u16 1#u16 (by simp) (by simp)
  let children : Slice U8 := Slice.from [0#u8,0#u8,0#u8,2#u8,0#u8,2#u8,195#u8,169#u8] (by scalar_tac)
  let text : Slice U8 := Slice.from [2#u8,0#u8,2#u8,195#u8,169#u8] (by scalar_tac)
  let utf8 : Slice U8 := Slice.from [195#u8,169#u8] (by scalar_tac)
  have leaf0 : __CORE__.scan children 1#u8 2#u16 =
      RustM.ok (some ⟨1#u16,3#usize⟩) := by
    simp [__CORE__.scan, children, h0, cast0, add0,
      Slice.index_usize, core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
      Lynx.Rust.Try.optionBranch, lift]
    change RustM.ok (some (⟨1#u16,3#usize⟩ : __CORE__.Scan)) = _
    rfl
  have converted : __PREFIX__.Extraction.Bytes.fromUtf8 utf8 = RustM.ok (.Ok utf8) :=
    __PREFIX__.Extraction.Bytes.valid utf8 (by decide +kernel)
  have leaf2 : __CORE__.scan text 1#u8 1#u16 =
      RustM.ok (some ⟨1#u16,5#usize⟩) := by
    simp [__CORE__.scan, text, h2, cast2, add2,
      Slice.index_usize, core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
      Lynx.Rust.Try.optionBranch, lift]
    change (do
      let r ← __PREFIX__.Extraction.Bytes.fromUtf8 utf8
      match r with
      | .Ok _ => RustM.ok (some (⟨1#u16,5#usize⟩ : __CORE__.Scan))
      | .Err _ => RustM.ok none) = _
    simp [converted]
  simp [__CORE__.scan, packet, h8, cast8, add8,
    Slice.index_usize, Slice.len, core.slice.Slice.get,
    core.slice.index.SliceIndexRangeUsizeSlice.get,
    Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]
  change __CORE__.scan_loop 2#u8 3#u16 11#usize
    (Slice.from [0#u8,0#u8,0#u8,2#u8,0#u8,2#u8,195#u8,169#u8] (by scalar_tac)) 1#u16 = _
  rw [__CORE__.scan_loop, loop.eq_1]
  dsimp only [children] at leaf0
  simp [__CORE__.scan_loop.body, subDepth, sub31, leaf0, add11,
    core.slice.Slice.get, core.slice.index.SliceIndexRangeFromUsizeSlice.get,
    Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]
  rw [loop.eq_1]
  dsimp only [text] at leaf2
  simp [Slice.drop, sub32, leaf2, add21,
    Lynx.Rust.Try.optionBranch, lift]
  rw [loop.eq_1]
  simp
theorem document_siblings : __ANALYSIS__.document_nodes packet 2#u8 3#u16 =
    RustM.ok (some 3#u16) := by
  have exactLength : 11#usize = Slice.len packet := by
    apply UScalar.eq_of_val_eq
    simp [packet]
  simp [__ANALYSIS__.document_nodes, siblings, lift,
    Lynx.Rust.Try.optionBranch, exactLength]

theorem too_shallow : __CORE__.scan packet 1#u8 3#u16 = RustM.ok none := by
  have h8 : core.num.U16.from_be_bytes (Array.make 2#usize [0#u8,8#u8]) = 8#u16 := by decide +kernel
  have cast8 : UScalar.cast .Usize 8#u16 = 8#usize := by scalar_tac
  have add8 := add_exact 8#usize 3#usize 11#usize (by scalar_tac) (by simp)
  have subDepth := sub_exact 1#u8 1#u8 0#u8 (by simp) (by simp)
  have sub31 := sub_exact 3#u16 1#u16 2#u16 (by simp) (by simp)
  simp [__CORE__.scan, packet, h8, cast8, add8,
    Slice.index_usize, core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
    Lynx.Rust.Try.optionBranch, lift]
  change __CORE__.scan_loop 1#u8 3#u16 11#usize
    (Slice.from [0#u8,0#u8,0#u8,2#u8,0#u8,2#u8,195#u8,169#u8] (by scalar_tac)) 1#u16 = _
  rw [__CORE__.scan_loop, loop.eq_1]
  simp [__CORE__.scan_loop.body, __CORE__.scan,
    subDepth, sub31, Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]


end __PREFIX__.Cases
