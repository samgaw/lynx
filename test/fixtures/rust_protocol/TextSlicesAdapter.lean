module
public import TextSlices.Properties
public import TextSlices.RustlerBridge
public section
open Aeneas Aeneas.Std
unseal RustM
namespace TextSlices.AdapterProperties

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

end TextSlices.AdapterProperties
