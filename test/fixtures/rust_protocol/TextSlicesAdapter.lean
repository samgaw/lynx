module
public import TextSlices.Properties
public import TextSlices.RustlerBridge
public section
open Aeneas Aeneas.Std
unseal RustM
namespace TextSlices.AdapterProperties

theorem equal_facade (left right : Str) :
    __EQUAL_NIF__ left right = .ok (decide (left.val = right.val)) := by
  simpa [__EQUAL_NIF__, lift] using TextSlices.Properties.text_equal_bytes left right

theorem prefix_facade (text needle : Str) :
    __PREFIX_NIF__ text needle =
      if needle.val.length ≤ text.val.length then
        .ok (decide (needle.val = text.val.take needle.val.length))
      else .ok false := by
  simpa [__PREFIX_NIF__, lift] using TextSlices.Properties.text_prefix_bytes text needle

theorem consume_facade (text needle : Str)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (needleValid : (TextSlices.Extraction.StringSlices.bytes needle).IsValidUTF8) :
    __CONSUME_NIF__ text needle =
      if needle.val.length ≤ text.val.length ∧ needle.val = text.val.take needle.val.length then
        .ok (some (text.drop (Slice.len needle)))
      else .ok none := by
  simpa [__CONSUME_NIF__, lift] using TextSlices.Properties.consume_exact text needle valid needleValid

theorem consume_encoding (input : Lynx.Term) (text needle field : Str)
    (env : Lynx.Rustler.Env)
    (decoded : Lynx.Rustler.decodeStr input = .ok text)
    (returned : __CONSUME_NIF__ text needle = .ok (some field))
    (bounded : field.val.length ≤ 4294967295) :
    Lynx.Rustler.Encoding.str field env =
      .ok (.bitstring (TextSlices.Extraction.StringSlices.bytes field) 0) := by
  apply Lynx.Rustler.Encoding.str_valid
  · apply TextSlices.Properties.consume_utf8 text needle field
      (Lynx.Rustler.decodeStr_utf8 input text decoded)
    simpa [__CONSUME_NIF__, lift] using returned
  · exact bounded

/-- Every field returned by the actual facade after successful text decoding
encodes as its exact UTF-8 binary, within the byte-offset output bound. -/
theorem window_encoding (input : Lynx.Term) (text field : Str) (start stop : U8)
    (env : Lynx.Rustler.Env)
    (decoded : Lynx.Rustler.decodeStr input = .ok text)
    (returned : __SLICE_NIF__ text start stop = .ok (some field)) :
    Lynx.Rustler.Encoding.str field env =
      .ok (.bitstring (TextSlices.Extraction.StringSlices.bytes field) 0) := by
  have valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8 :=
    Lynx.Rustler.decodeStr_utf8 input text decoded
  have call : experiment_nif.experiment_analysis.text_window text
      (UScalar.cast .Usize start) (UScalar.cast .Usize stop) = .ok (some field) := by
    simpa [__SLICE_NIF__, lift] using returned
  have range : TextSlices.Extraction.StringSlices.rangeGet
      ⟨UScalar.cast .Usize start, UScalar.cast .Usize stop⟩ text = .ok (some field) := call
  apply Lynx.Rustler.Encoding.str_valid
  · exact TextSlices.Extraction.StringSlices.rangeGet_valid_utf8 _ _ _ valid range
  · have size := TextSlices.Extraction.StringSlices.rangeGet_size _ _ _ range
    simp only [U8.cast_Usize_val_eq] at size
    have bounded : stop.val ≤ 255 := by scalar_tac
    omega

theorem checked_facade_utf8 (input : Lynx.Term) (text left right : Str) (position : U8)
    (decoded : Lynx.Rustler.decodeStr input = .ok text)
    (returned : __CHECKED_NIF__ text position = .ok (some (left, right))) :
    (TextSlices.Extraction.StringSlices.bytes left).IsValidUTF8 ∧
      (TextSlices.Extraction.StringSlices.bytes right).IsValidUTF8 := by
  have valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8 :=
    Lynx.Rustler.decodeStr_utf8 input text decoded
  have call : experiment_nif.experiment_analysis.checked_text_split text
      (UScalar.cast .Usize position) = .ok (some (left, right)) := by
    simpa [__CHECKED_NIF__, lift] using returned
  exact TextSlices.Properties.checked_utf8 _ _ _ _ valid call

end TextSlices.AdapterProperties
