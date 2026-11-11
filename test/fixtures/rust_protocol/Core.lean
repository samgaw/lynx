module
public import Protocol.Extraction.Funs
public section
open Aeneas Aeneas.Std experiment_core
set_option linter.unusedSimpArgs false
namespace Protocol.Properties

private theorem eq_ok {α : Type} {computation : RustM α} {value : α}
    (checked : WP.spec computation (fun result => result = value)) : computation = .ok value := by
  cases computation with
  | ret result => have equal := (WP.spec_ok result).mp checked; subst result; rfl
  | vis event continuation => simp at checked
  | div => simp at checked

theorem add_exact (x y z : Usize) (equal : x.val + y.val = z.val) :
    x + y = RustM.ok z := by
  apply eq_ok
  apply WP.spec_mono (UScalar.add_bv_spec (x := x) (y := y) (by scalar_tac))
  intro result found
  apply UScalar.eq_of_val_eq
  omega

theorem first_spec (input : Slice U8) (value : U8) (found : input.val[0]? = some value) :
    protocol.first input = RustM.ok value := by
  simp [protocol.first, Slice.index_usize, found]

theorem first_empty : protocol.first (Slice.new U8) = .fail .panic := by
  simp [protocol.first, Slice.index_usize]

theorem split_panic (input : Slice U8) (position : Usize)
    (outside : input.val.length < position.val) :
    protocol.prefix_length input position = .fail .panic := by
  simp [protocol.prefix_length, core.slice.Slice.split_at, UScalar.le_equiv,
    Nat.not_le.mpr outside]

theorem split_spec (input : Slice U8) (position : Usize)
    (inside : position.val ≤ input.val.length) :
    ∃ count, protocol.prefix_length input position = .ok count ∧ count.val = position.val := by
  simp [protocol.prefix_length, core.slice.Slice.split_at, UScalar.le_equiv, inside,
    List.splitAt_eq, List.length_take, Nat.min_eq_left inside]

theorem utf8_valid (input : Slice U8)
    (valid : (Protocol.Extraction.Bytes.bytes input).validateUTF8 = true) :
    ∃ count, protocol.utf8_status input = .ok (.Ok count) ∧ count.val = input.val.length := by
  rw [protocol.utf8_status, Protocol.Extraction.Bytes.valid input valid]
  simp only [bind_ok, lift]
  refine ⟨_, rfl, ?_⟩
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  · simp
  · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

theorem utf8_error (input : Slice U8) (error : experiment_core.core.str.error.Utf8Error)
    (rejected : Protocol.Extraction.Bytes.fromUtf8 input = RustM.ok (.Err error)) :
    protocol.utf8_status input = .ok (.Err (UScalar.cast .U64 error.valid_up_to,
      error.error_len.getD 0#u8)) := by
  have roundtrip (value : U8) : UScalar.cast .U8 (UScalar.cast .Usize value) = value := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
      cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
    · rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
      · scalar_tac
      · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  simp [protocol.utf8_status, rejected, lift, Protocol.Extraction.Bytes.errorLen,
    Protocol.Extraction.Bytes.validUpTo]
  cases error.error_len <;> simp [roundtrip]

theorem short (input : Slice U8) (bound : input.val.length < 2) :
    protocol.parse_frame input = .ok (.Err 1#u8) := by
  simp [protocol.parse_frame, UScalar.lt_equiv, bound]

/-- Version rejection precedes length and text validation for every complete header. -/
theorem wrong_version (input payload : Slice U8) (version length : U8)
    (shape : input.val = [version, length] ++ payload.val)
    (unsupported : version ≠ 1#u8) :
    protocol.parse_frame input = .ok (.Err 2#u8) := by
  have unsupported_val : version.val ≠ 1 := by
    intro equal
    apply unsupported
    apply UScalar.eq_of_val_eq
    simpa using equal
  simp [protocol.parse_frame, Slice.index_usize, shape, UScalar.lt_equiv, unsupported_val]

/-- Both truncation and trailing data are rejected before UTF-8 conversion. -/
theorem wrong_length (input payload : Slice U8) (length : U8)
    (shape : input.val = [1#u8, length] ++ payload.val)
    (mismatch : payload.val.length ≠ length.val) :
    protocol.parse_frame input = .ok (.Err 3#u8) := by
  have count_val : (UScalar.cast .Usize length).val = length.val := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  let total : Usize := Usize.ofNatCore (length.val + 2) (by scalar_tac)
  have added : UScalar.cast .Usize length + 2#usize = RustM.ok total := by
    apply add_exact
    simp [total, count_val]
  have different : payload.val.length + 1 + 1 ≠ total.val := by
    simp [total]
    omega
  simp [protocol.parse_frame, Slice.index_usize, shape, UScalar.lt_equiv,
    lift, added, different]

/-- Success requires the canonical version and exact consumption, with a bounded payload. -/
theorem accepted_shape (input payload : Slice U8) (version length : U8) (count : U64)
    (shape : input.val = [version, length] ++ payload.val)
    (accepted : protocol.parse_frame input = .ok (.Ok count)) :
    version = 1#u8 ∧ payload.val.length = length.val ∧
      input.val.length = length.val + 2 ∧ payload.val.length ≤ 255 := by
  have canonical : version = 1#u8 := by
    by_contra unsupported
    rw [wrong_version input payload version length shape unsupported] at accepted
    have impossible := RustM.ok_injective accepted
    cases impossible
  subst version
  have exact_length : payload.val.length = length.val := by
    by_contra mismatch
    rw [wrong_length input payload length shape mismatch] at accepted
    have impossible := RustM.ok_injective accepted
    cases impossible
  refine ⟨rfl, exact_length, ?_, ?_⟩
  · simp [shape, exact_length]
  · rw [exact_length]
    scalar_tac

theorem parse_valid (input payload : Slice U8) (length : U8)
    (shape : input.val = [1#u8, length] ++ payload.val)
    (size : payload.val.length = length.val)
    (valid : (Protocol.Extraction.Bytes.bytes payload).validateUTF8 = true) :
    protocol.parse_frame input = .ok (.Ok (UScalar.cast .U64 length)) := by
  let count := UScalar.cast .Usize length
  have count_val : count.val = length.val := by
    dsimp [count]
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  let total : Usize := Usize.ofNatCore (length.val + 2) (by scalar_tac)
  have added : count + 2#usize = RustM.ok total := by
    apply add_exact
    simp [total, count_val]
  have total_length : Slice.len input = total := by
    apply UScalar.eq_of_val_eq
    simp [shape, total, size]
  have split : core.slice.Slice.split_at input 2#usize =
      .ok (Slice.from [1#u8, length] (by scalar_tac), payload) := by
    simp [core.slice.Slice.split_at, shape]
  have converted : UScalar.cast .U64 count = UScalar.cast .U64 length := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    · rw [count_val, UScalar.cast_val_mod_pow_greater_numBits_eq]
      decide
    · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  have not_short : ¬ total.val ≤ 1 := by simp [total]
  dsimp [count] at added converted
  simp [protocol.parse_frame, Slice.index_usize, shape, UScalar.lt_equiv,
    lift, added, total_length, split, Protocol.Extraction.Bytes.valid payload valid, converted, not_short]

@[expose] def frame : Slice U8 := Slice.from [1#u8, 2#u8, 195#u8, 169#u8] (by scalar_tac)
theorem unicode_frame : protocol.parse_frame frame = .ok (.Ok 2#u64) := by
  have cast8 : UScalar.cast .Usize 2#u8 = 2#usize := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have cast64 : UScalar.cast .U64 2#usize = 2#u64 := by
    apply UScalar.eq_of_val_eq
    scalar_tac
  have added : (2#usize + 2#usize) = RustM.ok 4#usize := by
    apply add_exact
    scalar_tac
  have utf8 : (⟨#[195,169]⟩ : ByteArray).IsValidUTF8 := by decide +kernel
  simp [protocol.parse_frame, frame, Slice.index_usize, core.slice.Slice.split_at,
    Protocol.Extraction.Bytes.fromUtf8, Protocol.Extraction.Bytes.bytes,
    UScalar.lt_equiv, UScalar.le_equiv, lift, cast8, cast64, added, utf8]

end Protocol.Properties
