module
public import SplitBuffer.Extraction.Funs
public section
open Aeneas Aeneas.Std atomic_analysis
namespace SplitBuffer.Properties
set_option maxHeartbeats 2000000

theorem split_exact (input : alloc.vec.Vec U8) (position : Usize)
    (inside : position.val ≤ input.val.length) (bound : input.val.length ≤ 262144) :
    atomic_core.frames.split_buffer input position =
      RustM.ok (alloc.vec.Vec.from (input.val.drop position.val) (by have h := input.property; simp only [List.length_drop]; omega),
        alloc.vec.Vec.from (input.val.take position.val) (by have h := input.property; simp only [List.length_take]; omega)) := by
  exact SplitBuffer.Extraction.VectorModel.split_off_eq input position inside bound

theorem split_panic (input : alloc.vec.Vec U8) (position : Usize)
    (outside : input.val.length < position.val) :
    atomic_core.frames.split_buffer input position = RustM.fail .panic := by
  exact SplitBuffer.Extraction.VectorModel.split_off_panic input position outside

theorem short (input : alloc.vec.Vec U8) (bound : input.val.length < 3) :
    take_frame input = RustM.ok (.Ok none, input) := by
  simp [take_frame, atomic_core.frames.take_frame, UScalar.lt_equiv, bound]

theorem wrong_version (input : alloc.vec.Vec U8) (version high low : U8) (rest : List U8)
    (shape : input.val = [version, high, low] ++ rest) (wrong : version ≠ 1#u8) :
    take_frame input = RustM.ok (.Err 1#u8, input) := by
  have slices : input.slice.val = [version, high, low] ++ rest := shape
  have different : version.val ≠ 1 := by
    intro equal
    apply wrong
    exact UScalar.eq_of_val_eq equal
  have not_short : ¬rest.length + 1 + 1 + 1 < 3 := by omega
  simp [take_frame, atomic_core.frames.take_frame, alloc.vec.Vec.index,
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
    ∃ frame rest, take_frame input = RustM.ok (.Ok (some frame), rest) ∧
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
  simp [take_frame, atomic_core.frames.take_frame, alloc.vec.Vec.index,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.index, Slice.index_usize,
    not_short, slices, UScalar.lt_equiv, lift, added, not_truncated, split,
    core.mem.replace, take, drop]

theorem truncated (input : alloc.vec.Vec U8) (high low : U8) (rest : List U8)
    (shape : input.val = [1#u8, high, low] ++ rest)
    (incomplete : rest.length < (core.num.U16.from_be_bytes (Array.make 2#usize [high, low])).val) :
    take_frame input = RustM.ok (.Ok none, input) := by
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
  simp [take_frame, atomic_core.frames.take_frame, alloc.vec.Vec.index,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.index, Slice.index_usize,
    not_short, slices, UScalar.lt_equiv, lift, added, truncated]

theorem split_cutoff (input : alloc.vec.Vec U8) (position : Usize)
    (inside : position.val ≤ input.val.length) (outside : ¬input.val.length ≤ 262144) :
    atomic_core.frames.split_buffer input position = RustM.fail .undef := by
  exact SplitBuffer.Extraction.VectorModel.split_off_cutoff input position inside outside

theorem split_preserves_bytes (input : alloc.vec.Vec U8) (position : Usize)
    (inside : position.val ≤ input.val.length) (bound : input.val.length ≤ 262144) :
    ∃ suffix retained, atomic_core.frames.split_buffer input position = RustM.ok (suffix, retained) ∧
      retained.val ++ suffix.val = input.val := by
  rw [split_exact input position inside bound]
  simp

end SplitBuffer.Properties
