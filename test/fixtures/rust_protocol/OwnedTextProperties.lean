module
public import OwnedText.Extraction.Funs
public section
open Aeneas Aeneas.Std experiment_analysis
namespace OwnedText.Properties
open OwnedText.Extraction

theorem decode_invalid (input : alloc.vec.Vec U8) (error : core.str.error.Utf8Error)
    (invalid : Bytes.fromUtf8 input.slice = .ok (.Err error)) :
    experiment_core.protocol.decode_owned input = .ok (.Err input) := by
  simp [experiment_core.protocol.decode_owned,OwnedString.fromUtf8,invalid,OwnedString.errorIntoBytes]

theorem roundtrip (input : alloc.vec.Vec U8) :
    experiment_core.protocol.owned_bytes_roundtrip input = .ok input := by
  by_cases valid : (Bytes.bytes input.slice).IsValidUTF8
  · have utf8 := ByteArray.validateUTF8_eq_true_iff.mpr valid
    have byteEquality : OwnedString.byteList (String.fromUTF8 (Bytes.bytes input.slice) valid) = input.val := by
      simpa [OwnedString.byteList,String.fromUTF8,alloc.vec.Vec.val] using Bytes.bytes_values input.slice
    have bound : (OwnedString.byteList (String.fromUTF8 (Bytes.bytes input.slice) valid)).length ≤ Usize.max := by
      rw [byteEquality]
      exact input.len_ineq
    have vectorEquality : (alloc.vec.Vec.mk (Slice.from _ bound)) = input := by
      apply alloc.vec.Vec.ext
      change (Slice.from _ bound).val = input.val
      simpa only [Slice.from_val] using byteEquality
    simp [experiment_core.protocol.owned_bytes_roundtrip,experiment_core.protocol.decode_owned,
      OwnedString.fromUtf8,Bytes.valid _ utf8,String.fromUTF8?,valid,OwnedString.intoBytes,bound,vectorEquality]
  · have utf8 : (Bytes.bytes input.slice).validateUTF8 = false := by
      exact Bool.eq_false_iff.mpr (fun h => valid (ByteArray.validateUTF8_eq_true_iff.mp h))
    obtain ⟨result,total⟩ := Bytes.fromUtf8_total input.slice
    cases result with
    | Err error => simp [experiment_core.protocol.owned_bytes_roundtrip,decode_invalid input error total]
    | Ok text =>
      simp only [Bytes.fromUtf8,utf8,Bool.false_eq_true,↓reduceIte] at total
      split at total <;> simp_all <;> split at total <;> simp_all

theorem composition (input : alloc.vec.Vec U8) : owned_bytes_roundtrip input = .ok input := by
  simp [owned_bytes_roundtrip,roundtrip]

@[expose] def broken : alloc.vec.Vec U8 := ⟨Slice.from [195#u8,40#u8] (by scalar_tac)⟩
theorem invalid_bytes : decode_owned broken = .ok (.Err broken) := by cbv
theorem non_ascii : decode_owned ⟨toStr "héllo"⟩ = .ok (.Ok "héllo") := by cbv
theorem append_unicode : append_owned "hé" (toStr "llo") = .ok "héllo" := by cbv
theorem append_spec (text suffix : String) (view : Str)
    (valid : String.fromUTF8? (Bytes.bytes view) = some suffix)
    (bound : (text ++ suffix).toByteArray.size ≤ 262144) :
    append_owned text view = .ok (text ++ suffix) := by
  have encoded : String.fromUTF8? ⟨(view.val.map (fun byte => UInt8.ofNat byte.val)).toArray⟩ = some suffix := valid
  simp only [append_owned,experiment_core.protocol.append_owned,OwnedString.pushStr,encoded,bound,↓reduceIte]

theorem append_cutoff (text suffix : String) (view : Str)
    (valid : String.fromUTF8? (Bytes.bytes view) = some suffix)
    (large : ¬(text ++ suffix).toByteArray.size ≤ 262144) :
    OwnedString.pushStr text view = RustM.fail .undef := by
  have encoded : String.fromUTF8? ⟨(view.val.map (fun byte => UInt8.ofNat byte.val)).toArray⟩ = some suffix := valid
  simp only [OwnedString.pushStr,encoded,large,↓reduceIte]
end OwnedText.Properties
