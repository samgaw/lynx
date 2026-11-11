module
public import TextViews.Extraction.Funs
public import TextViews.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace TextViews.Properties

private theorem widen8 (value : U8) : (UScalar.cast .Usize value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem widen64 (value : Usize) : (UScalar.cast .U64 value).val = value.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

theorem core_bytes (text : Str) : experiment_nif.experiment_core.protocol.text_bytes text = RustM.ok (α := Slice U8) text := by
  rfl

theorem payload_spec (input : Slice U8) (header : U8)
    (valid : (TextViews.Extraction.Bytes.bytes input).validateUTF8 = true) :
    experiment_nif.experiment_analysis.text_payload_bytes input header = RustM.ok (.Ok
      (if header.val ≤ input.val.length then some (input.drop (UScalar.cast .Usize header)) else none)) := by
  rw [experiment_nif.experiment_analysis.text_payload_bytes, TextViews.Extraction.Bytes.valid input valid, bind_ok]
  dsimp only
  rw [core_bytes input]
  rw [bind_ok (α := Slice U8) (β := core.result.Result (Option (Slice U8)) U8)]
  by_cases h : header.val ≤ input.val.length
  all_goals simp [core.slice.Slice.get, core.slice.index.SliceIndexRangeFromUsizeSlice.get,
    widen8, h, lift, bind_ok]

theorem exact_bytes (input : Slice U8) (header : U8)
    (valid : (TextViews.Extraction.Bytes.bytes input).validateUTF8 = true) :
    (do let result ← experiment_nif.experiment_analysis.text_payload_bytes input header
        pure (match result with
          | .Ok payload => payload.map (fun bytes => bytes.val)
          | .Err _ => none)) = RustM.ok
      (if header.val ≤ input.val.length then some (input.val.drop header.val) else none) := by
  rw [payload_spec input header valid]
  split <;> simp_all [pure, Slice.drop, widen8]

def lengths (input : Slice U8) (header : U8) : Option U64 :=
  if header.val ≤ input.val.length then
    some (UScalar.cast .U64 (Slice.len (input.drop (UScalar.cast .Usize header)))) else none

theorem caller_spec (input : Slice U8) (header : U8)
    (valid : (TextViews.Extraction.Bytes.bytes input).validateUTF8 = true) :
    experiment_nif.experiment_analysis.text_payload_length input header = RustM.ok (.Ok (lengths input header)) := by
  by_cases h : header.val ≤ input.val.length
  all_goals simp [experiment_nif.experiment_analysis.text_payload_length, payload_spec input header valid, lengths, h,
    core.option.Option.map,
    experiment_nif.experiment_analysis.text_payload_length.closure.Insts.CoreOpsFunctionFnOnceTupleShared0SliceU8U64.call_once]

theorem lengths_values (input : Slice U8) (header : U8) :
    (lengths input header).map (fun count => count.val) =
      if header.val ≤ input.val.length then some (input.val.length - header.val) else none := by
  by_cases h : header.val ≤ input.val.length
  all_goals simp [lengths, h, widen64, widen8, Slice.len, Slice.drop]

theorem invalid_spec (input : Slice U8) (header : U8)
    (error : experiment_nif.core.str.error.Utf8Error)
    (rejected : TextViews.Extraction.Bytes.fromUtf8 input = RustM.ok (.Err error)) :
    experiment_nif.experiment_analysis.text_payload_bytes input header = RustM.ok (.Err 4#u8) ∧
      experiment_nif.experiment_analysis.text_payload_length input header = RustM.ok (.Err 4#u8) := by
  simp [experiment_nif.experiment_analysis.text_payload_bytes, experiment_nif.experiment_analysis.text_payload_length, rejected]

@[expose] def unicode : Slice U8 := .from [195#u8, 169#u8] (by scalar_tac)

theorem unicode_valid : (TextViews.Extraction.Bytes.bytes unicode).validateUTF8 = true := by
  decide +kernel

theorem inside_character :
    (do let result ← experiment_nif.experiment_analysis.text_payload_bytes unicode 1#u8
        pure (match result with
          | .Ok payload => payload.map (fun bytes => bytes.val)
          | .Err _ => none)) = RustM.ok (some [169#u8]) := by
  rw [exact_bytes unicode 1#u8 unicode_valid]
  apply congrArg RustM.ok
  decide +kernel

theorem facade_unicode (header : U8) :
    __FACADE__ ⟨#[195,169]⟩ header = RustM.ok (.Ok (lengths unicode header)) := by
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[195,169]⟩ = RustM.ok unicode := by
    have unsigned : 2 ≤ Usize.max := by scalar_tac
    have signed : (⟨#[195,169]⟩ : ByteArray).size ≤ Isize.max.toNat := by
      change 2 ≤ Isize.max.toNat
      scalar_tac
    simp [Lynx.Rustler.binaryAsSlice, unicode, unsigned, signed]
    rfl
  simp [__FACADE__, decoded, caller_spec unicode header unicode_valid]

theorem facade_inside_character :
    __FACADE__ ⟨#[195,169]⟩ 1#u8 = RustM.ok (.Ok (some 1#u64)) := by
  rw [facade_unicode]
  apply congrArg RustM.ok
  apply congrArg core.result.Result.Ok
  simp [lengths, unicode]
  apply UScalar.eq_of_val_eq
  simp [widen64, widen8, Slice.len, Slice.drop, unicode]

theorem facade_truncated :
    __FACADE__ ⟨#[195,169]⟩ 3#u8 = RustM.ok (.Ok none) := by
  rw [facade_unicode]
  congr 1

@[expose] def invalidInput : Slice U8 := .from [255#u8] (by scalar_tac)

theorem facade_invalid (header : U8) :
    __FACADE__ ⟨#[255]⟩ header = RustM.ok (.Err 4#u8) := by
  have unsigned : 1 ≤ Usize.max := by scalar_tac
  have signed : (⟨#[255]⟩ : ByteArray).size ≤ Isize.max.toNat := by
    change 1 ≤ Isize.max.toNat
    scalar_tac
  have decoded : Lynx.Rustler.binaryAsSlice ⟨#[255]⟩ = RustM.ok invalidInput := by
    simp [Lynx.Rustler.binaryAsSlice, invalidInput, unsigned, signed]
    rfl
  have bad : (TextViews.Extraction.Bytes.bytes invalidInput).validateUTF8 = false := by
    decide +kernel
  have found : TextViews.Extraction.Bytes.errorOffset (invalidInput.val.length + 1)
      (TextViews.Extraction.Bytes.bytes invalidInput).toList 0 = some (0, some 1) := by
    decide +kernel
  have rejected := TextViews.Extraction.Bytes.invalid invalidInput bad 0 (some 1) found (Nat.zero_le _)
  have computed := (invalid_spec invalidInput header _ rejected).2
  simp [__FACADE__, decoded, computed]

end TextViews.Properties
