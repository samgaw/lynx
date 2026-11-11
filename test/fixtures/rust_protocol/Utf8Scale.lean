module
public import Protocol.Extraction.Funs
public section
open Aeneas Aeneas.Std
namespace Protocol.Utf8Scale

-- The computation is extracted Rust; UTF-8 validation remains an explicitly
-- reported standard-library model. Symbolic prefix proofs avoid byte-by-byte
-- kernel evaluation at concrete protocol sizes.

def fromBytes (data : List UInt8) (bound : data.length ≤ Usize.max) : Slice U8 :=
  Slice.from (data.map fun b => (⟨b.toBitVec⟩ : U8)) (by simpa only [List.length_map] using bound)

theorem bytes_fromBytes (data : List UInt8) (bound : data.length ≤ Usize.max) :
    Protocol.Extraction.Bytes.bytes (fromBytes data bound) = data.toByteArray := by
  have cancel : (fun b : UInt8 => UInt8.ofNat ((⟨b.toBitVec⟩ : U8).val)) = id := by
    funext b
    change UInt8.ofNat b.toNat = b
    simp
  simp only [Protocol.Extraction.Bytes.bytes, fromBytes, Slice.from_val, List.map_map, Function.comp_def, cancel, List.map_id]
  apply ByteArray.ext
  simp

theorem toList_data (bs : ByteArray) : bs.toList = bs.data.toList := by
  have loop (i : Nat) (r : List UInt8) (inside : i ≤ bs.size) :
      ByteArray.toList.loop bs i r = r.reverse ++ bs.data.toList.drop i := by
    fun_induction ByteArray.toList.loop bs i r with
    | case1 i r h ih =>
      rw [ih (by omega)]
      simp only [List.reverse_cons, List.append_assoc]
      congr 1
      conv_rhs => rw [List.drop_eq_getElem_cons (by simpa only [Array.length_toList, ByteArray.size_data] using h)]
      simp [ByteArray.get!]
      exact getElem!_pos bs.data i (show i < bs.data.size from h)
    | case2 i r h =>
      have last : i = bs.size := by omega
      simp [last]
  simpa [ByteArray.toList] using loop 0 [] (Nat.zero_le _)

theorem ascii_prefix (n fuel offset : Nat) (rest : List UInt8) :
    Protocol.Extraction.Bytes.errorOffset (n + fuel) (List.replicate n 65 ++ rest) offset =
      Protocol.Extraction.Bytes.errorOffset fuel rest (offset + n) := by
  induction n generalizing offset with
  | zero => simp
  | succ n ih =>
    simp only [Nat.succ_add, List.replicate_succ, List.cons_append,
      Protocol.Extraction.Bytes.errorOffset, Protocol.Extraction.Bytes.next]
    simp only [show (65 : UInt8) < 128 by decide, ↓reduceIte]
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (offset + 1)

theorem ascii_invalid (n : Nat) (suffix : List UInt8)
    (invalid : suffix.toByteArray.validateUTF8 = false) :
    (List.replicate n (65 : UInt8) ++ suffix).toByteArray.validateUTF8 = false := by
  rw [ByteArray.validateUTF8_eq_false_iff] at invalid ⊢
  induction n with
  | zero => simpa using invalid
  | succ n ih =>
    have step : (List.replicate (n+1) (65 : UInt8) ++ suffix).toByteArray =
        ['A'].utf8Encode ++ (List.replicate n (65 : UInt8) ++ suffix).toByteArray := by
      change _ = ([65] : List UInt8).toByteArray ++ _
      rw [← List.toByteArray_append]
      simp [List.replicate_succ]
    rw [step, ByteArray.isValidUTF8_utf8Encode_singleton_append_iff]
    exact ih

theorem valid_string (text : String) (bound : text.utf8ByteSize ≤ Usize.max) :
    ∃ count, experiment_core.protocol.utf8_status
      (fromBytes text.toByteArray.data.toList (by simpa only [Array.length_toList, ByteArray.size_data, String.size_toByteArray] using bound)) = RustM.ok (.Ok count) ∧
      count.val = text.utf8ByteSize := by
  have valid : (Protocol.Extraction.Bytes.bytes
      (fromBytes text.toByteArray.data.toList (by simpa only [Array.length_toList, ByteArray.size_data, String.size_toByteArray] using bound))).validateUTF8 = true := by
    rw [bytes_fromBytes, ByteArray.validateUTF8_eq_true_iff]
    convert text.isValidUTF8 using 1
    apply ByteArray.ext
    simp only [List.data_toByteArray, Array.toArray_toList]
  simp only [experiment_core.protocol.utf8_status,
    Protocol.Extraction.Bytes.valid _ valid, bind_ok, lift]
  refine ⟨_, rfl, ?_⟩
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  · change (fromBytes text.toByteArray.data.toList _).val.length = _
    simp only [fromBytes, Slice.from_val, List.length_map, Array.length_toList, ByteArray.size_data, String.size_toByteArray]
  · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

def invalidInput (n : Nat) (bound : n + 1 ≤ Usize.max) : Slice U8 :=
  fromBytes (List.replicate n (65 : UInt8) ++ [255]) (by simpa using bound)

theorem invalid_suffix (n : Nat) (bound : n + 1 ≤ Usize.max) :
    ∃ offset, experiment_core.protocol.utf8_status (invalidInput n bound) = RustM.ok (.Err (offset, 1#u8)) ∧
      offset.val = n := by
  dsimp only [invalidInput]
  let input := fromBytes (List.replicate n (65 : UInt8) ++ [255]) (by simpa using bound)
  have valid : (Protocol.Extraction.Bytes.bytes input).validateUTF8 = false := by
    rw [bytes_fromBytes]
    exact ascii_invalid n [255] (by decide +kernel)
  have scan : Protocol.Extraction.Bytes.errorOffset (input.val.length + 1)
      (Protocol.Extraction.Bytes.bytes input).toList 0 = some (n, some 1) := by
    rw [bytes_fromBytes, toList_data]
    simp only [List.data_toByteArray, List.toList_toArray]
    have size : input.val.length + 1 = n + 2 := by simp [input, fromBytes]
    rw [size, ascii_prefix]
    simp [Protocol.Extraction.Bytes.errorOffset, Protocol.Extraction.Bytes.next]
  have rejected := Protocol.Extraction.Bytes.invalid input valid n (some 1) scan (by omega)
  have one : UScalar.cast .U8 (UScalar.cast .Usize (⟨BitVec.ofNat 8 1⟩ : U8)) = 1#u8 := by
    apply UScalar.eq_of_val_eq
    rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
      · decide +kernel
      · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
    · rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
      · scalar_tac
      · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  change ∃ offset, experiment_core.protocol.utf8_status input = RustM.ok (.Err (offset, 1#u8)) ∧ offset.val = n
  simp only [experiment_core.protocol.utf8_status,
    rejected, bind_ok, lift, Protocol.Extraction.Bytes.errorLen,
    Protocol.Extraction.Bytes.validUpTo, Option.map, one]
  refine ⟨_, rfl, ?_⟩
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  · change (BitVec.ofNat UScalarTy.Usize.numBits n).toNat = n
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := bound
    scalar_tac
  · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

def truncatedInput (n : Nat) (bound : n + 1 ≤ Usize.max) : Slice U8 :=
  fromBytes (List.replicate n (65 : UInt8) ++ [194]) (by simpa using bound)

theorem truncated_suffix (n : Nat) (bound : n + 1 ≤ Usize.max) :
    ∃ offset, experiment_core.protocol.utf8_status (truncatedInput n bound) = RustM.ok (.Err (offset, 0#u8)) ∧
      offset.val = n := by
  dsimp only [truncatedInput]
  let input := fromBytes (List.replicate n (65 : UInt8) ++ [194]) (by simpa using bound)
  have valid : (Protocol.Extraction.Bytes.bytes input).validateUTF8 = false := by
    rw [bytes_fromBytes]
    exact ascii_invalid n [194] (by decide +kernel)
  have scan : Protocol.Extraction.Bytes.errorOffset (input.val.length + 1)
      (Protocol.Extraction.Bytes.bytes input).toList 0 = some (n, none) := by
    rw [bytes_fromBytes, toList_data]
    simp only [List.data_toByteArray, List.toList_toArray]
    have size : input.val.length + 1 = n + 2 := by simp [input, fromBytes]
    rw [size, ascii_prefix]
    simp [Protocol.Extraction.Bytes.errorOffset, Protocol.Extraction.Bytes.next]
  have rejected := Protocol.Extraction.Bytes.invalid input valid n none scan (by omega)
  change ∃ offset, experiment_core.protocol.utf8_status input = RustM.ok (.Err (offset, 0#u8)) ∧ offset.val = n
  simp only [experiment_core.protocol.utf8_status,
    rejected, bind_ok, lift, Protocol.Extraction.Bytes.errorLen,
    Protocol.Extraction.Bytes.validUpTo, Option.map]
  refine ⟨_, rfl, ?_⟩
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  · change (BitVec.ofNat UScalarTy.Usize.numBits n).toNat = n
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt]
    have := bound
    scalar_tac
  · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

theorem repeated_unicode_size (n : Nat) :
    (String.ofList (List.replicate n '😀')).utf8ByteSize = n * 4 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    rw [List.replicate_succ]
    change (String.ofList (['😀'] ++ List.replicate n '😀')).utf8ByteSize = _
    rw [String.ofList_append, String.utf8ByteSize_append, ih]
    have char_size : (String.ofList ['😀']).utf8ByteSize = 4 := by decide +kernel
    rw [char_size]
    omega

def unicodeInput (n : Nat) (bound : n * 4 ≤ Usize.max) : Slice U8 :=
  fromBytes (String.ofList (List.replicate n '😀')).toByteArray.data.toList (by
    simpa only [Array.length_toList, ByteArray.size_data, String.size_toByteArray,
      repeated_unicode_size] using bound)

theorem repeated_unicode (n : Nat) (bound : n * 4 ≤ Usize.max) :
    ∃ count, experiment_core.protocol.utf8_status (unicodeInput n bound) = RustM.ok (.Ok count) ∧
      count.val = n * 4 := by
  simpa only [unicodeInput, repeated_unicode_size] using
    valid_string (String.ofList (List.replicate n '😀')) (by simpa only [repeated_unicode_size] using bound)

theorem megabyte_unicode :
    ∃ count, experiment_core.protocol.utf8_status (unicodeInput 262144 (by scalar_tac)) =
      RustM.ok (.Ok count) ∧ count.val = 1048576 := by
  simpa only [Nat.reduceMul] using repeated_unicode 262144 (by scalar_tac)

theorem megabyte_invalid :
    ∃ offset, experiment_core.protocol.utf8_status (invalidInput 1048576 (by scalar_tac)) =
      RustM.ok (.Err (offset, 1#u8)) ∧ offset.val = 1048576 := by
  exact invalid_suffix 1048576 (by scalar_tac)

theorem megabyte_truncated :
    ∃ offset, experiment_core.protocol.utf8_status (truncatedInput 1048576 (by scalar_tac)) =
      RustM.ok (.Err (offset, 0#u8)) ∧ offset.val = 1048576 := by
  exact truncated_suffix 1048576 (by scalar_tac)

end Protocol.Utf8Scale
