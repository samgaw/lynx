module
public import __PREFIX__.StringViewsModel
public section
open Aeneas Aeneas.Std
unseal RustM
namespace __PREFIX__.StringSlices

@[expose] def get {I Output : Type}
    (inst : core.slice.index.SliceIndex I Str Output) (text : Str) (index : I) :
    RustM (Option Output) := inst.get index text

@[expose] def rangeGet (range : core.ops.range.Range Usize) (text : Str) :
    RustM (Option Str) :=
  if __PREFIX__.StringViews.isCharBoundary text range.start &&
      __PREFIX__.StringViews.isCharBoundary text range.end then
    core.slice.index.SliceIndexRangeUsizeSlice.get range text
  else .ok none

@[expose] def fromGet (range : core.ops.range.RangeFrom Usize) (text : Str) :
    RustM (Option Str) := rangeGet ⟨range.start, Slice.len text⟩ text

@[expose] def toGet (range : core.ops.range.RangeTo Usize) (text : Str) :
    RustM (Option Str) := rangeGet ⟨0#usize, range.end⟩ text

@[expose] def bytes (text : Str) : ByteArray :=
  ⟨(text.val.map (fun byte => UInt8.ofNat byte.val)).toArray⟩

@[simp] theorem size_bytes (text : Str) : (bytes text).size = text.val.length := by
  simp [bytes, ByteArray.size]

theorem bytes_slice (text : Str) (start stop : Nat)
    (bound : (text.val.slice start stop).length ≤ Usize.max) :
    bytes (Slice.from (text.val.slice start stop) bound) = (bytes text).extract start stop := by
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [bytes, List.slice, ByteArray.data_extract, List.extract]

private theorem encode_byte_bound (c : Char) (byte : UInt8) (member : byte ∈ String.utf8EncodeChar c) :
    byte.toNat < 248 := by
  unfold String.utf8EncodeChar at member
  dsimp only at member
  split at member
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    subst byte
    simp only [UInt8.toNat_ofNat', Nat.reducePow]
    omega
  · split at member
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [UInt8.toNat_ofNat', Nat.reducePow] <;> omega
    · split at member
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp only [UInt8.toNat_ofNat', Nat.reducePow] <;> omega
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> simp only [UInt8.toNat_ofNat', Nat.reducePow] <;> omega

private theorem valid_byte_bound (data : ByteArray) (valid : data.IsValidUTF8)
    (i : Nat) (bound : i < data.size) : data[i].toNat < 248 := by
  obtain ⟨chars, rfl⟩ := valid
  simp only [List.utf8Encode, List.getElem_toByteArray]
  have index : i < (chars.flatMap String.utf8EncodeChar).length := by
    simpa only [List.utf8Encode, List.size_toByteArray] using bound
  have member : (chars.flatMap String.utf8EncodeChar)[i]'index ∈ chars.flatMap String.utf8EncodeChar :=
    List.getElem_mem _
  obtain ⟨c, _, member⟩ := List.mem_flatMap.mp member
  exact encode_byte_bound c _ member

private theorem first_byte_cases : ∀ value : Fin 248,
    (UInt8.ofNat value.val).IsUTF8FirstByte ↔ value.val < 128 ∨ 192 ≤ value.val := by
  decide +kernel

private theorem first_byte_iff (byte : UInt8) (bound : byte.toNat < 248) :
    byte.IsUTF8FirstByte ↔ byte.toNat < 128 ∨ 192 ≤ byte.toNat := by
  simpa using first_byte_cases ⟨byte.toNat, bound⟩

theorem boundary_valid (text : Str) (valid : (bytes text).IsValidUTF8) (position : Usize)
    (boundary : __PREFIX__.StringViews.isCharBoundary text position = true) :
    String.Pos.Raw.IsValid ⟨bytes text, valid⟩ ⟨position.val⟩ := by
  by_cases zero : position.val = 0
  · rw [zero]
    exact String.Pos.Raw.isValid_zero
  · by_cases inside : position.val < text.val.length
    · have insideBytes : position.val < (bytes text).size := by simpa using inside
      apply String.Pos.Raw.isValid_iff_isUTF8FirstByte.mpr
      refine Or.inr ⟨?_, ?_⟩
      · simpa [String.Pos.Raw.lt_iff, String.rawEndPos, String.utf8ByteSize] using insideBytes
      · rw [String.getUTF8Byte_eq_getElem]
        apply (first_byte_iff _ (valid_byte_bound (bytes text) valid position.val insideBytes)).mpr
        have byteBound : (text.val[position.val]'inside).val < 256 := by scalar_tac
        simpa [__PREFIX__.StringViews.isCharBoundary, zero,
          List.getElem?_eq_getElem, inside, bytes, ByteArray.getElem_eq_getElem_data,
          UInt8.toNat_ofNat', Nat.mod_eq_of_lt byteBound] using boundary
    · have absent : text.val[position.val]? = none := List.getElem?_eq_none (by omega)
      have atEnd : position.val = text.val.length := by
        simpa [__PREFIX__.StringViews.isCharBoundary, zero, absent] using boundary
      have ending : (⟨position.val⟩ : String.Pos.Raw) = (⟨bytes text, valid⟩ : String).rawEndPos := by
        ext
        simpa [String.rawEndPos, String.utf8ByteSize] using atEnd
      rw [ending]
      exact String.Pos.Raw.isValid_rawEndPos

theorem rangeGet_valid_utf8 (range : core.ops.range.Range Usize) (text field : Str)
    (valid : (bytes text).IsValidUTF8) (returned : rangeGet range text = .ok (some field)) :
    (bytes field).IsValidUTF8 := by
  unfold rangeGet at returned
  unfold Str at returned
  split at returned
  · rename_i boundaries
    have both : __PREFIX__.StringViews.isCharBoundary text range.start = true ∧
        __PREFIX__.StringViews.isCharBoundary text range.end = true := by
      simpa only [Bool.and_eq_true] using boundaries
    unfold core.slice.index.SliceIndexRangeUsizeSlice.get at returned
    split at returned
    · rename_i bounds
      have equal := Option.some.inj (RustM.ok_injective returned)
      subst field
      rw [bytes_slice]
      exact (String.Pos.Raw.isValidUTF8_extract_iff (s := ⟨bytes text, valid⟩)
        ⟨range.start.val⟩ ⟨range.end.val⟩
        (by simpa [String.Pos.Raw.le_iff, UScalar.le_equiv] using bounds.1)
        (by simpa [String.Pos.Raw.le_iff, String.rawEndPos, String.utf8ByteSize, Slice.length] using bounds.2)).mpr
        (Or.inr ⟨boundary_valid text valid range.start both.1, boundary_valid text valid range.end both.2⟩)
    · simp at returned
  · simp at returned

theorem rangeGet_size (range : core.ops.range.Range Usize) (text field : Str)
    (returned : rangeGet range text = .ok (some field)) : field.val.length ≤ range.end.val := by
  unfold rangeGet Str at returned
  split at returned
  · unfold core.slice.index.SliceIndexRangeUsizeSlice.get at returned
    split at returned
    · have equal := Option.some.inj (RustM.ok_injective returned)
      subst field
      rw [Slice.from_val, List.slice_length]
      omega
    · simp at returned
  · simp at returned

theorem rangeGet_returns (range : core.ops.range.Range Usize) (text : Str) :
    ∃ result, rangeGet range text = .ok result := by
  unfold rangeGet Str
  split
  · unfold core.slice.index.SliceIndexRangeUsizeSlice.get
    split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩


-- Unsupported dictionary slots exhaust verification. They are not native
-- outcomes and cannot establish successful execution of an unchecked operation.
@[expose] def RangeIndex : core.slice.index.SliceIndex (core.ops.range.Range Usize) Str Str := {
  get := rangeGet
  get_mut := fun _ _ => .fail .undef
  get_unchecked := fun _ _ => .fail .undef
  get_unchecked_mut := fun _ _ => .fail .undef
  index := fun _ _ => .fail .undef
  index_mut := fun _ _ => .fail .undef
}
@[expose] def RangeFromIndex : core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) Str Str := {
  get := fromGet
  get_mut := fun _ _ => .fail .undef
  get_unchecked := fun _ _ => .fail .undef
  get_unchecked_mut := fun _ _ => .fail .undef
  index := fun _ _ => .fail .undef
  index_mut := fun _ _ => .fail .undef
}
@[expose] def RangeToIndex : core.slice.index.SliceIndex (core.ops.range.RangeTo Usize) Str Str := {
  get := toGet
  get_mut := fun _ _ => .fail .undef
  get_unchecked := fun _ _ => .fail .undef
  get_unchecked_mut := fun _ _ => .fail .undef
  index := fun _ _ => .fail .undef
  index_mut := fun _ _ => .fail .undef
}
end __PREFIX__.StringSlices
