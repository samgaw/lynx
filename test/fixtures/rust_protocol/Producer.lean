module
public import __PREFIX__.Extraction.Funs
public section
set_option autoImplicit false
open Aeneas Aeneas.Std
namespace __PREFIX__.Properties

private theorem pushed (output : alloc.vec.Vec U8) (byte : U8)
    (room : output.val.length < 262144) :
    ∃ next, __PREFIX__.Extraction.VectorModel.push output byte = RustM.ok next ∧
      next.val = output.val ++ [byte] := by
  rw [__PREFIX__.Extraction.VectorModel.push_eq]
  simp only [room, ↓reduceDIte]
  exact ⟨_, rfl, by simp⟩

theorem copy_bytes (iter : core.slice.iter.Iter U8) (output : alloc.vec.Vec U8)
    (cursor : iter.i ≤ iter.slice.val.length)
    (room : output.val.length + (iter.slice.val.length - iter.i) ≤ 262144) :
    Aeneas.Std.WP.spec (__CORE__.encode_binary_loop iter output)
      (fun result => result.val = output.val ++ iter.slice.val.drop iter.i) := by
  let expected := output.val ++ iter.slice.val.drop iter.i
  have expectedBound : expected.length ≤ 262144 := by simp only [expected, List.length_append, List.length_drop]; exact room
  unfold __CORE__.encode_binary_loop
  refine loop.spec_decr_nat (fun state : core.slice.iter.Iter U8 × alloc.vec.Vec U8 => state.1.slice.val.length - state.1.i)
    (fun state => state.1.i ≤ state.1.slice.val.length ∧ state.2.val ++ state.1.slice.val.drop state.1.i = expected)
    (fun result : alloc.vec.Vec U8 => result.val = expected) _ _ ?_ ⟨cursor, rfl⟩
  rintro ⟨current, bytes⟩ ⟨within, conservation⟩
  dsimp only at within conservation
  by_cases inside : current.i < current.slice.val.length
  · have size := congrArg List.length conservation
    simp only [List.length_append, List.length_drop] at size
    obtain ⟨next, returned, nextValue⟩ := pushed bytes current.slice.val[current.i] (by omega)
    have dropped : current.slice.val.drop current.i =
        current.slice.val[current.i] :: current.slice.val.drop (current.i + 1) :=
      List.drop_eq_getElem_cons inside
    have preserved : next.val ++ current.slice.val.drop (current.i + 1) = expected := by
      rw [nextValue, List.append_assoc]
      simpa only [List.singleton_append, dropped] using conservation
    simp only [__CORE__.encode_binary_loop.body,
      core.slice.iter.IteratorSliceIter.next, Slice.len_val, inside, ↓reduceDIte, bind_ok]
    change Aeneas.Std.WP.spec (do
      let output1 ← __PREFIX__.Extraction.VectorModel.push bytes current.slice.val[current.i]
      RustM.ok (ControlFlow.cont (β := alloc.vec.Vec U8)
        (({slice := current.slice, i := current.i + 1} : core.slice.iter.Iter U8), output1))) _
    rw [returned]
    simp only [bind_ok, Aeneas.Std.WP.spec_ok]
    exact ⟨⟨by omega, preserved⟩, by omega⟩
  · have last : current.i = current.slice.val.length := by omega
    simp [last] at conservation
    simp [__CORE__.encode_binary_loop.body,
      core.slice.iter.IteratorSliceIter.next, inside, conservation,
      Aeneas.Std.WP.spec_ok]

@[expose] def header (payload : Slice U8) : Array U8 2#usize :=
  core.num.U16.to_be_bytes (UScalar.cast .U16 (Slice.len payload))

theorem encode_bytes (payload : Slice U8) (bound : payload.val.length ≤ 65535) :
    ∃ result, __CORE__.encode_binary payload = RustM.ok (some result) ∧
      result.val = [0#u8, (header payload).val[0], (header payload).val[1]] ++ payload.val := by
  have maximum : (UScalar.cast .Usize core.num.U16.MAX).val = 65535 := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    · simp [core.num.U16.MAX, U16.rMax]
    · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  have allowed : ¬Slice.len payload > UScalar.cast .Usize core.num.U16.MAX := by
    simp only [UScalar.lt_equiv, Slice.len_val, Slice.length, maximum]
    omega
  have indexed0 : Array.index_usize (header payload) 0#usize = RustM.ok (header payload).val[0] := by
    simp [Array.index_usize]
  have indexed1 : Array.index_usize (header payload) 1#usize = RustM.ok (header payload).val[1] := by
    simp [Array.index_usize]
  obtain ⟨first, pushed0, firstValue⟩ := pushed (alloc.vec.Vec.new U8) 0#u8 (by simp [alloc.vec.Vec.new])
  obtain ⟨second, pushed1, secondValue⟩ := pushed first (header payload).val[0] (by simp_all [alloc.vec.Vec.new])
  obtain ⟨third, pushed2, thirdValue⟩ := pushed second (header payload).val[1] (by simp_all [alloc.vec.Vec.new])
  have thirdBytes : third.val = [0#u8, (header payload).val[0], (header payload).val[1]] := by
    simp_all [alloc.vec.Vec.new]
  have copied := copy_bytes ⟨payload, 0⟩ third (by simp) (by simp [thirdBytes]; omega)
  obtain ⟨result, returned, value⟩ := triple_iff_exists_ok.mp (Aeneas.Std.WP.spec_to_mvcgen copied)
  refine ⟨result, ?_, ?_⟩
  · simp only [__CORE__.encode_binary, lift, bind_ok, allowed, ↓reduceIte]
    change (do
      let first ← __PREFIX__.Extraction.VectorModel.push (alloc.vec.Vec.new U8) 0#u8
      let a ← Array.index_usize (header payload) 0#usize
      let second ← __PREFIX__.Extraction.VectorModel.push first a
      let b ← Array.index_usize (header payload) 1#usize
      let third ← __PREFIX__.Extraction.VectorModel.push second b
      let iter ← SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter payload
      let output ← __CORE__.encode_binary_loop iter third
      RustM.ok (some output)) = _
    simp [pushed0, pushed1, pushed2, indexed0, indexed1,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter, returned]
  · simpa [thirdBytes] using value

private theorem endian_roundtrip (value : U16) :
    core.num.U16.from_be_bytes (core.num.U16.to_be_bytes value) = value := by
  apply UScalar.eq_of_val_eq
  change (BitVec.fromBEBytes ((core.num.U16.to_be_bytes value).val.map U8.bv)).toNat = _
  rw [core.num.U16.to_be_bytes, Array.from_val]
  simp only [BitVec.fromBEBytes, BitVec.toNat_cast]
  rw [BitVec.toBEBytes, List.map_reverse, List.map_reverse, List.reverse_reverse, List.map_map]
  change (BitVec.fromLEBytes (List.map id value.bv.toLEBytes)).toNat = _
  rw [List.map_id, BitVec.fromLEBytes_toLEBytes (by decide : 16 % 8 = 0)]
  rfl

private theorem header_data (payload : Slice U8) :
    (header payload).val = [(header payload).val[0], (header payload).val[1]] := by
  apply List.ext_getElem
  · simp
  · intro i inside other
    simp only [List.length_cons, List.length_nil] at other
    have choices : i = 0 ∨ i = 1 := by omega
    rcases choices with rfl | rfl <;> simp

private theorem header_value (payload : Slice U8) :
    core.num.U16.from_be_bytes (Array.make 2#usize [(header payload).val[0], (header payload).val[1]]) =
      UScalar.cast .U16 (Slice.len payload) := by
  have reconstructed : Array.make 2#usize [(header payload).val[0], (header payload).val[1]] = header payload := by
    apply Aeneas.Std.Array.ext
    simp only [Array.make, Array.from_val]
    exact (header_data payload).symm
  rw [reconstructed]
  exact endian_roundtrip _

private theorem header_length (payload : Slice U8) (bound : payload.val.length ≤ 65535) :
    (UScalar.cast .Usize (UScalar.cast .U16 (Slice.len payload))).val = payload.val.length := by
  rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
  · rw [UScalar.cast_val_mod_pow_of_inBounds_eq]
    · simp
    · scalar_tac
  · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem add_exact {ty} (a b : UScalar ty) (safe : a.val + b.val ≤ UScalar.max ty) :
    ∃ result, a + b = RustM.ok result ∧ result.val = a.val + b.val := by
  obtain ⟨result, returned, facts⟩ := triple_iff_exists_ok.mp
    (Aeneas.Std.WP.spec_to_mvcgen (UScalar.add_bv_spec safe))
  exact ⟨result, returned, facts.1⟩

theorem encode_decode (payload : Slice U8) (bound : payload.val.length ≤ 65535) :
    ∃ encoded, __CORE__.encode_binary payload = RustM.ok (some encoded) ∧
      __CORE__.decode_binary (alloc.vec.Vec.deref encoded) = RustM.ok (some payload) := by
  obtain ⟨encoded, produced, value⟩ := encode_bytes payload bound
  let input := alloc.vec.Vec.deref encoded
  have bytes : input.val = [0#u8, (header payload).val[0], (header payload).val[1]] ++ payload.val := by
    simpa [input, alloc.vec.Vec.deref] using value
  let length := UScalar.cast .Usize (UScalar.cast .U16 (Slice.len payload))
  have lengthValue : length.val = payload.val.length := header_length payload bound
  obtain ⟨total, added, totalValue⟩ := add_exact length 3#usize (by scalar_tac)
  have exactLength : total = Slice.len input := by
    apply UScalar.eq_of_val_eq
    simp only [Slice.len_val, Slice.length, bytes, List.length_append, List.length_cons, List.length_nil]
    simp at totalValue
    omega
  have totalLower : 3 ≤ total.val := by simp at totalValue; omega
  have totalFits : total.val ≤ payload.val.length + 1 + 1 + 1 := by simp at totalValue; omega
  have notShort : ¬payload.val.length + 1 + 1 + 1 < 3 := by omega
  dsimp only [length] at added
  have scanned : __CORE__.scan input 1#u8 1#u16 =
      RustM.ok (some ⟨1#u16,total⟩) := by
    simp [__CORE__.scan, bytes, Slice.index_usize, header_value,
      added, core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get,
      totalLower, totalFits, notShort, Lynx.Rust.Try.optionBranch, lift]
    change RustM.ok (some (⟨1#u16,total⟩ : __CORE__.Scan)) = _
    rfl
  refine ⟨encoded, produced, ?_⟩
  change __CORE__.decode_binary input = _
  simp [__CORE__.decode_binary, bytes, notShort,
    Slice.index_usize, scanned, exactLength, Lynx.Rust.Try.optionBranch, lift,
    core.slice.Slice.get, core.slice.index.SliceIndexRangeUsizeSlice.get]

theorem binary_roundtrip (payload : Slice U8) (bound : payload.val.length ≤ 65535) :
    __ANALYSIS__.binary_roundtrip payload = RustM.ok (some true) := by
  obtain ⟨encoded, produced, decoded⟩ := encode_decode payload bound
  have comparison := core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 payload payload
    (by intro x y; simp [Aeneas.Std.WP.spec_ok])
  obtain ⟨result, equal, correct⟩ := triple_iff_exists_ok.mp (Aeneas.Std.WP.spec_to_mvcgen comparison)
  have yes : result = true := correct.mpr rfl
  simp [__ANALYSIS__.binary_roundtrip, produced, decoded, equal, yes,
    Lynx.Rust.Try.optionBranch, lift]

theorem encode_oversize (payload : Slice U8) (bound : 65535 < payload.val.length) :
    __CORE__.encode_binary payload = RustM.ok none := by
  have maximum : (UScalar.cast .Usize core.num.U16.MAX).val = 65535 := by
    rw [UScalar.cast_val_mod_pow_greater_numBits_eq]
    · simp [core.num.U16.MAX, U16.rMax]
    · cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]
  simp [__CORE__.encode_binary, lift, UScalar.lt_equiv, maximum, bound]

theorem roundtrip_oversize (payload : Slice U8) (bound : 65535 < payload.val.length) :
    __ANALYSIS__.binary_roundtrip payload = RustM.ok none := by
  simp [__ANALYSIS__.binary_roundtrip, encode_oversize payload bound,
    Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]

end __PREFIX__.Properties
