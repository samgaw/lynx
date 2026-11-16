module
public import FrameRuntime.Extraction.Funs
public section
attribute [local simp] Lynx.NativeM.ok Lynx.NativeM.lift
open Aeneas Aeneas.Std atomic_analysis
namespace FrameRuntime.Properties
set_option maxHeartbeats 2000000

theorem split_exact (input : alloc.vec.Vec U8) (position : Usize)
    (inside : position.val ≤ input.val.length) (bound : input.val.length ≤ 262144) :
    atomic_core.frames.split_buffer input position =
      Lynx.NativeM.ok (alloc.vec.Vec.from (input.val.drop position.val) (by have h := input.property; simp only [List.length_drop]; omega),
        alloc.vec.Vec.from (input.val.take position.val) (by have h := input.property; simp only [List.length_take]; omega)) := by
  simpa [atomic_core.frames.split_buffer] using congrArg Lynx.NativeM.fromRust (FrameRuntime.Extraction.VectorModel.split_off_eq input position inside bound)

theorem split_panic (input : alloc.vec.Vec U8) (position : Usize)
    (outside : input.val.length < position.val) :
    atomic_core.frames.split_buffer input position = Lynx.NativeM.fail .panic := by
  simpa [atomic_core.frames.split_buffer] using congrArg Lynx.NativeM.fromRust (FrameRuntime.Extraction.VectorModel.split_off_panic input position outside)

theorem short (input : alloc.vec.Vec U8) (bound : input.val.length < 3) :
    atomic_core.frames.take_frame input = Lynx.NativeM.ok (.Ok none, input) := by
  simp [atomic_core.frames.take_frame, UScalar.lt_equiv, bound]

theorem wrong_version (input : alloc.vec.Vec U8) (version high low : U8) (rest : List U8)
    (shape : input.val = [version, high, low] ++ rest) (wrong : version ≠ 1#u8) :
    atomic_core.frames.take_frame input = Lynx.NativeM.ok (.Err 1#u8, input) := by
  have slices : input.slice.val = [version, high, low] ++ rest := shape
  have different : version.val ≠ 1 := by
    intro equal
    apply wrong
    exact UScalar.eq_of_val_eq equal
  have not_short : ¬rest.length + 1 + 1 + 1 < 3 := by omega
  simp [atomic_core.frames.take_frame, alloc.vec.Vec.index,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    core.slice.index.Usize.index, Slice.index_usize, shape, slices, UScalar.lt_equiv, different, not_short]

private theorem eq_ok {α : Type} {computation : RustM α} {value : α}
    (checked : WP.spec computation (fun result => result = value)) : computation = .ok value := by
  cases computation with
  | ret result => have equal := (WP.spec_ok result).mp checked; subst result; rfl
  | vis event continuation => simp at checked
  | div => simp at checked

private theorem add_exact (x y z : Usize) (equal : x.val + y.val = z.val) :
    x + y = RustM.ok z := by
  apply eq_ok
  apply WP.spec_mono (UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  intro result found
  apply UScalar.eq_of_val_eq
  omega

theorem consumes_exact (input : alloc.vec.Vec U8) (high low : U8) (payload tail : List U8)
    (shape : input.val = [1#u8, high, low] ++ payload ++ tail)
    (wire : (core.num.U16.from_be_bytes (Array.make 2#usize [high, low])).val = payload.length)
    (bound : input.val.length ≤ 262144) :
    ∃ frame rest, atomic_core.frames.take_frame input = Lynx.NativeM.ok (.Ok (some frame), rest) ∧
      frame.val = [1#u8, high, low] ++ payload ∧ rest.val = tail := by
  let length := core.num.U16.from_be_bytes (Array.make 2#usize [high, low])
  have count_val : (UScalar.cast .Usize length).val = length.val := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  let finish := Usize.ofNatCore (3 + length.val) (by scalar_tac)
  have added : 3#usize + UScalar.cast .Usize length = RustM.ok finish := by
    apply add_exact
    simp [finish, count_val]
  dsimp [length] at added
  have not_short : ¬input.val.length < 3 := by simp [shape] <;> omega
  have not_truncated : ¬input.val.length < finish.val := by
    simp [finish, length, wire, shape] <;> omega
  have inside : finish.val ≤ input.val.length := by omega
  have slices : input.slice.val = [1#u8, high, low] ++ payload ++ tail := shape
  have split := split_exact input finish inside bound
  have take : input.val.take finish.val = [1#u8, high, low] ++ payload := by
    have equal : finish.val = ([1#u8, high, low] ++ payload).length := by simp [finish, length, wire] <;> omega
    rw [equal, shape]
    simp
  have drop : input.val.drop finish.val = tail := by
    have equal : finish.val = ([1#u8, high, low] ++ payload).length := by simp [finish, length, wire] <;> omega
    rw [equal, shape]
    simp
  simp [atomic_core.frames.take_frame, alloc.vec.Vec.index,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.index, Slice.index_usize,
    not_short, slices, UScalar.lt_equiv, lift, added, not_truncated, split,
    core.mem.replace, take, drop]

-- Values fitting u32 fit both supported Rust machine-word widths. Preserve
-- the upstream checked failure test for larger values.
@[cbv_eval] theorem try_usize_eq (value : Nat) :
    UScalar.tryMk .Usize value =
      if small : value < 4294967296 then
        RustM.ok (UScalar.ofNatCore (ty := .Usize) value (by
          cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits] <;> omega))
      else RustM.ofOption
        (if bounded : value < 2 ^ UScalarTy.Usize.numBits then
          some (UScalar.ofNatCore (ty := .Usize) value bounded) else none) .panic := by
  split
  · have bounded : value < 2 ^ UScalarTy.Usize.numBits := by
      cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits] <;> omega
    simp only [UScalarTy.numBits] at bounded
    simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, UScalarTy.numBits, bounded]
  · simp [UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds, UScalarTy.numBits]

@[cbv_eval] theorem widen16 (value : U16) : UScalar.cast .Usize value =
    Usize.ofNatCore value.val (by
      cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits] <;> scalar_tac) := by
  apply UScalar.eq_of_val_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalar.cast_val_eq, UScalarTy.numBits]
  all_goals scalar_tac

private theorem header_add_evaluation :
    UScalar.add (3#usize) (65535#usize) = RustM.ok (65538#usize) := by
  cbv

theorem truncated (input : alloc.vec.Vec U8) (high low : U8) (rest : List U8)
    (shape : input.val = [1#u8, high, low] ++ rest)
    (incomplete : rest.length < (core.num.U16.from_be_bytes (Array.make 2#usize [high, low])).val) :
    atomic_core.frames.take_frame input = Lynx.NativeM.ok (.Ok none, input) := by
  let length := core.num.U16.from_be_bytes (Array.make 2#usize [high, low])
  have count_val : (UScalar.cast .Usize length).val = length.val := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  let finish := Usize.ofNatCore (3 + length.val) (by scalar_tac)
  have added : 3#usize + UScalar.cast .Usize length = RustM.ok finish := by
    apply add_exact
    simp [finish, count_val]
  dsimp [length] at added
  have not_short : ¬input.val.length < 3 := by simp [shape] <;> omega
  have truncated : input.val.length < finish.val := by
    simp [shape, finish, length]
    omega
  have slices : input.slice.val = [1#u8, high, low] ++ rest := shape
  simp [atomic_core.frames.take_frame, alloc.vec.Vec.index,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.index, Slice.index_usize,
    not_short, slices, UScalar.lt_equiv, lift, added, truncated]

theorem split_cutoff (input : alloc.vec.Vec U8) (position : Usize)
    (inside : position.val ≤ input.val.length) (outside : ¬input.val.length ≤ 262144) :
    atomic_core.frames.split_buffer input position = Lynx.Result.error .exhausted := by
  simpa [atomic_core.frames.split_buffer] using congrArg Lynx.NativeM.fromRust (FrameRuntime.Extraction.VectorModel.split_off_cutoff input position inside outside)

/-- Parsing either returns normally or reaches the explicit allocation bound; it never panics. -/
theorem no_panic (input : alloc.vec.Vec U8) :
    (∃ result, atomic_core.frames.take_frame input = Lynx.NativeM.ok result) ∨
      atomic_core.frames.take_frame input = Lynx.Result.error .exhausted := by
  cases shape : input.val with
  | nil =>
    left
    exact ⟨_, short input (by simp [shape])⟩
  | cons version rest =>
    cases rest with
    | nil =>
      left
      exact ⟨_, short input (by simp [shape])⟩
    | cons high rest =>
      cases rest with
      | nil =>
        left
        exact ⟨_, short input (by simp [shape])⟩
      | cons low rest =>
        have bytes : input.val = [version, high, low] ++ rest := shape
        by_cases wrong : version ≠ 1#u8
        · exact Or.inl ⟨_, wrong_version input version high low rest bytes wrong⟩
        have version_eq : version = 1#u8 := Classical.not_not.mp wrong
        subst version
        let length := core.num.U16.from_be_bytes (Array.make 2#usize [high, low])
        have count_val : (UScalar.cast .Usize length).val = length.val := by
          rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
          cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
        let finish := Usize.ofNatCore (3 + length.val) (by scalar_tac)
        have added : 3#usize + UScalar.cast .Usize length = RustM.ok finish := by
          apply add_exact
          simp [finish, count_val]
        dsimp [length] at added
        by_cases incomplete : rest.length < length.val
        · exact Or.inl ⟨_, truncated input high low rest bytes incomplete⟩
        have inside : finish.val ≤ input.val.length := by
          simp [finish, bytes]
          omega
        have not_short : ¬input.val.length < 3 := by simp [bytes]
        have not_truncated : ¬input.val.length < finish.val := by omega
        have slices : input.slice.val = [1#u8, high, low] ++ rest := bytes
        by_cases bound : input.val.length ≤ 262144
        · have split := split_exact input finish inside bound
          left
          simp [atomic_core.frames.take_frame, alloc.vec.Vec.index,
            core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.index,
            Slice.index_usize, not_short, slices, UScalar.lt_equiv, lift, added,
            not_truncated, split, core.mem.replace]
        · have split := split_cutoff input finish inside bound
          right
          simp [atomic_core.frames.take_frame, alloc.vec.Vec.index,
            core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.index,
            Slice.index_usize, not_short, slices, UScalar.lt_equiv, lift, added,
            not_truncated, split]

end FrameRuntime.Properties
