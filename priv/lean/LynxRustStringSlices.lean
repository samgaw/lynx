module
public import __PREFIX__.StringViewsModel
public section
open Aeneas Aeneas.Std
unseal RustM
namespace __PREFIX__.StringSlices

/-- The caller must establish the shared-borrow precondition. Invalid positions
exhaust verification; they are not modelled Rust outcomes. -/
@[expose] def splitUnchecked (text : Str) (position : Usize) : RustM (Str × Str) :=
  if __PREFIX__.StringViews.isCharBoundary text position then
    core.slice.Slice.split_at text position
  else .fail .undef

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

/-- Only called by the extracted standard prefix remover after its check.
Invalid offsets exhaust verification rather than becoming native outcomes. -/
@[expose] def uncheckedFrom (text : Str) (range : core.ops.range.RangeFrom Usize) : RustM Str := do
  match ← fromGet range text with
  | some field => .ok field
  | none => .fail .undef

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

theorem boundary_of_valid (text : Str) (valid : (bytes text).IsValidUTF8) (position : Usize)
    (atBoundary : String.Pos.Raw.IsValid ⟨bytes text, valid⟩ ⟨position.val⟩) :
    __PREFIX__.StringViews.isCharBoundary text position = true := by
  by_cases zero : position.val = 0
  · simp [__PREFIX__.StringViews.isCharBoundary, zero]
  rcases String.Pos.Raw.isValid_iff_isUTF8FirstByte.mp atBoundary with ending | ⟨inside, first⟩
  · have endingValue := congrArg String.Pos.Raw.byteIdx ending
    have equal : position.val = text.val.length := by
      simpa [String.rawEndPos, String.utf8ByteSize] using endingValue
    simp [__PREFIX__.StringViews.isCharBoundary, zero, equal]
  · have insideBytes : position.val < (bytes text).size := by
      simpa [String.Pos.Raw.lt_iff, String.rawEndPos, String.utf8ByteSize] using inside
    have insideList : position.val < text.val.length := by simpa using insideBytes
    rw [String.getUTF8Byte_eq_getElem] at first
    have classified := (first_byte_iff _ (valid_byte_bound (bytes text) valid position.val insideBytes)).mp first
    have byteBound : (text.val[position.val]'insideList).val < 256 := by scalar_tac
    simpa [__PREFIX__.StringViews.isCharBoundary, zero, List.getElem?_eq_getElem, insideList,
      bytes, ByteArray.getElem_eq_getElem_data, UInt8.toNat_ofNat', Nat.mod_eq_of_lt byteBound] using classified

theorem prefix_boundary (text needle : Str)
    (valid : (bytes text).IsValidUTF8) (needleValid : (bytes needle).IsValidUTF8)
    (matched : needle.val = text.val.take needle.val.length)
    (bounded : needle.val.length ≤ text.val.length) :
    __PREFIX__.StringViews.isCharBoundary text (Slice.len needle) = true := by
  apply boundary_of_valid text valid
  have converted : bytes needle = (bytes text).extract 0 needle.val.length := by
    have sliceEq : text.val.slice 0 needle.val.length = needle.val := by
      simpa only [List.slice, List.drop_zero, Nat.sub_zero] using matched.symm
    have bound : (text.val.slice 0 needle.val.length).length ≤ Usize.max := by
      rw [sliceEq]
      exact Slice.property needle
    have equality : needle = Slice.from (text.val.slice 0 needle.val.length) bound := by
      apply (Slice.eq_iff _ _).mpr
      simpa only [Slice.from_val] using sliceEq.symm
    calc
      bytes needle = bytes (Slice.from (text.val.slice 0 needle.val.length) bound) := congrArg bytes equality
      _ = (bytes text).extract 0 needle.val.length := bytes_slice text 0 needle.val.length bound
  have extracted : ((bytes text).extract 0 needle.val.length).IsValidUTF8 := by
    rwa [← converted]
  have ends := (String.Pos.Raw.isValidUTF8_extract_iff (s := ⟨bytes text, valid⟩)
    ⟨0⟩ ⟨needle.val.length⟩ (by simp [String.Pos.Raw.le_iff])
    (by simpa [String.Pos.Raw.le_iff, String.rawEndPos, String.utf8ByteSize] using bounded)).mp extracted
  rcases ends with equal | ⟨_, ending⟩
  · have zero : needle.val.length = 0 := by simpa using (congrArg String.Pos.Raw.byteIdx equal).symm
    simpa [Slice.len, zero] using (String.Pos.Raw.isValid_zero (s := ⟨bytes text, valid⟩))
  · simpa [Slice.len] using ending

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


theorem uncheckedFrom_valid_utf8 (text field : Str) (range : core.ops.range.RangeFrom Usize)
    (valid : (bytes text).IsValidUTF8) (returned : uncheckedFrom text range = .ok field) :
    (bytes field).IsValidUTF8 := by
  obtain ⟨result, computation⟩ := rangeGet_returns ⟨range.start, Slice.len text⟩ text
  have borrowed : fromGet range text = .ok result := computation
  simp only [uncheckedFrom, borrowed, bind_ok] at returned
  cases result with
  | none => simp at returned
  | some value =>
    have equality : value = field := by simpa using returned
    subst field
    exact rangeGet_valid_utf8 _ _ _ valid computation

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
