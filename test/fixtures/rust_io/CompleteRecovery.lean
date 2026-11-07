module
public import Record.WriteInterrupted
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.CompleteRecovery
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.LockedProperties Record.LockedConcurrent Record.RepairCrashProperties
  Record.MalformedProperties

private theorem decode_accepted (value : U16) (a b c d : U8)
    (accepted : io_core.decode_record (word a b) (word c d) = NativeM.ok (some value)) :
    word a b ^^^ word c d = core.num.U16.MAX ∧ word a b = value := by
  by_cases good : word a b ^^^ word c d = core.num.U16.MAX
  · exact ⟨good, by simpa [decode_spec, good, NativeM.ok] using accepted⟩
  · simp [decode_spec, good, NativeM.ok] at accepted

private theorem ones_bit (i : Nat) (small : i < 16) : (65535#16).getLsbD i = true := by
  interval_cases i <;> decide

private theorem accepted_layout (value : U16) (a b c d : U8)
    (accepted : io_core.decode_record (word a b) (word c d) = NativeM.ok (some value)) :
    [a,b,c,d] = (layout value).val := by
  obtain ⟨check, candidate⟩ := decode_accepted value a b c d accepted
  have bits := congrArg UScalar.bv check
  have found := congrArg UScalar.bv candidate
  have equal : a.bv = (low value).bv ∧ b.bv = (high value).bv ∧
      c.bv = (low (~~~value)).bv ∧ d.bv = (high (~~~value)).bv := by
    simp only [word_bv, low, high, UScalar.bv_xor, UScalar.bv_not,
      core.num.U16.MAX, UScalar.ofNat, UScalar.ofNatCore_bv, U16.rMax,
      UScalarTy.numBits, U8.bv] at bits found ⊢
    rw [found] at bits
    refine ⟨?_, ?_, ?_, ?_⟩
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have range : i < 8 := by simpa only [UScalarTy.numBits] using hi
      have candidateBit := congrArg (fun (x : BitVec 16) => x.getLsbD i) found
      interval_cases i <;>
        simp only [BitVec.getLsbD_append] at candidateBit ⊢
      all_goals simp_all
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have range : i < 8 := by simpa only [UScalarTy.numBits] using hi
      have candidateBit := congrArg (fun (x : BitVec 16) => x.getLsbD (i + 8)) found
      interval_cases i <;>
        simp only [BitVec.getLsbD_append] at candidateBit ⊢
      all_goals simp_all
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have range : i < 8 := by simpa only [UScalarTy.numBits] using hi
      have checkBit := congrArg (fun (x : BitVec 16) => x.getLsbD i) bits
      rw [ones_bit i (by omega)] at checkBit
      interval_cases i <;>
        simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append] at checkBit ⊢
      all_goals (simp_all; grind)
    · apply BitVec.eq_of_getLsbD_eq
      intro i hi
      have range : i < 8 := by simpa only [UScalarTy.numBits] using hi
      have checkBit := congrArg (fun (x : BitVec 16) => x.getLsbD (i + 8)) bits
      rw [ones_bit (i + 8) (by omega)] at checkBit
      interval_cases i <;>
        simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append] at checkBit ⊢
      all_goals (simp_all; grind)
  have first : a = low value := UScalar.eq_of_val_eq (congrArg BitVec.toNat equal.1)
  have second : b = high value := UScalar.eq_of_val_eq (congrArg BitVec.toNat equal.2.1)
  have third : c = low (~~~value) := UScalar.eq_of_val_eq (congrArg BitVec.toNat equal.2.2.1)
  have fourth : d = high (~~~value) := UScalar.eq_of_val_eq (congrArg BitVec.toNat equal.2.2.2)
  simp [layout, first, second, third, fourth]

/-- The acknowledged prefix followed by up to four zero/new bytes from one
actual appended record. A complete unacknowledged record is permitted. -/
@[expose] def AppendImage (values : List U16) (value : U16) (data : ByteArray) : Prop :=
  let head := disk (logBytes values)
  Prefix head data ∧ data.size ≤ head.size + 4 ∧
    ∀ i, head.size ≤ i → i < data.size →
      data[i]! = 0 ∨ data[i]! = (encoded value)[i - head.size]!

/-- Any number of admitted persistence choices preserves both the complete
prefix and the original appended value's byte identities. -/
theorem persist_append_image (values : List U16) (value : U16) (old visible mask result : ByteArray)
    (oldImage : AppendImage values value old) (visibleImage : AppendImage values value visible)
    (accepted : persist old visible mask = some result) : AppendImage values value result := by
  have sizes := persist_lengths old visible mask result accepted
  refine ⟨⟨by have := oldImage.1.1; have := visibleImage.1.1; omega, ?_⟩,
    by have := oldImage.2.1; have := visibleImage.2.1; omega, ?_⟩
  · intro i inside
    rw [persist_at old visible mask result accepted i (by
      have := oldImage.1.1; have := visibleImage.1.1; omega)]
    split
    · exact visibleImage.1.2 i inside
    · exact oldImage.1.2 i inside
  · intro i afterHead inside
    rw [persist_at old visible mask result accepted i inside]
    split
    · by_cases bound : i < visible.size
      · exact visibleImage.2.2 i afterHead bound
      · left; rw [getElem!_neg visible i bound]; rfl
    · by_cases bound : i < old.size
      · exact oldImage.2.2 i afterHead bound
      · left; rw [getElem!_neg old i bound]; rfl

private theorem prefix_shape (values : List U16) (data : ByteArray)
    (preserved : Prefix (disk (logBytes values)) data) :
    ∃ tail : List U8, data = disk (logBytes values ++ tail) ∧
      tail.length = data.size - (disk (logBytes values)).size := by
  let head := disk (logBytes values)
  have equal : data.data.toList.take head.size = head.data.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, _root_.Array.length_toList, ← ByteArray.size_data]
      exact Nat.min_eq_left preserved.1
    · intro i hi hj
      have inside : i < head.size := by simpa only [_root_.Array.length_toList, ← ByteArray.size_data] using hj
      have bytes := preserved.2 i inside
      rw [getElem!_pos data i (by have bound : head.size ≤ data.size := preserved.1; omega), getElem!_pos head i inside] at bytes
      simpa only [List.getElem_take, _root_.Array.getElem_toList, ByteArray.getElem_eq_getElem_data] using bytes
  let tail := (data.data.toList.drop head.size).map byteValue
  refine ⟨tail, ?_, ?_⟩
  · have reconstruct := List.take_append_drop head.size data.data.toList
    rw [equal] at reconstruct
    have headRoundtrip : head.data.toList.map byteValue = logBytes values := by
      simp [head, disk, List.map_map, Function.comp_def, byte_roundtrip]
    have decoded := congrArg (List.map byteValue) reconstruct
    simp only [List.map_append, headRoundtrip] at decoded
    rw [← disk_roundtrip data, ← decoded]
  · simp [tail, head, ← ByteArray.size_data]

private theorem tail_at (head tail : List U8) (i : Nat) (inside : i < tail.length) :
    (disk (head ++ tail))[head.length + i]! = (disk tail)[i]! := by
  rw [getElem!_pos _ _ (by simp [disk, ← ByteArray.size_data]; omega),
    getElem!_pos _ i (by simp [disk, ← ByteArray.size_data]; omega)]
  simp [disk, ByteArray.getElem_eq_getElem_data, List.getElem_append_right]

/-- Recover a fresh-slot invariant from an arbitrary complete-prefix image. -/
theorem append_image_shape (values : List U16) (value : U16) (data : ByteArray)
    (image : AppendImage values value data) :
    ∃ tail : List U8, data = disk (logBytes values ++ tail) ∧ Fresh value (disk tail) := by
  obtain ⟨tail, contents, length⟩ := prefix_shape values data image.1
  refine ⟨tail, contents, ?_, ?_⟩
  · have bound := image.2.1
    have tailBound : tail.length ≤ 4 := by omega
    simpa [disk, ← ByteArray.size_data] using tailBound
  · intro i inside
    have small : i < tail.length := by simpa [disk, ← ByteArray.size_data] using inside
    have start : (disk (logBytes values)).size = (logBytes values).length := by simp [disk, ← ByteArray.size_data]
    have atByte := image.2.2 ((logBytes values).length + i) (by omega) (by
      rw [contents]; simp [disk, ← ByteArray.size_data]; omega)
    rw [contents, tail_at _ _ i small] at atByte
    simpa only [start, Nat.add_sub_cancel_left] using atByte

/-- Construct the append invariant from a fresh tail at the end of the log. -/
theorem append_fresh_image (values : List U16) (value : U16) (tail : List U8)
    (fresh : Fresh value (disk tail)) : AppendImage values value (disk (logBytes values ++ tail)) := by
  have headSize : (disk (logBytes values)).size = (logBytes values).length := by simp [disk, ← ByteArray.size_data]
  have tailSize : (disk tail).size = tail.length := by simp [disk, ← ByteArray.size_data]
  refine ⟨prefix_append _ _, ?_, ?_⟩
  · have bound := fresh.1
    simp only [disk, ← ByteArray.size_data, _root_.List.size_toArray, List.length_map, List.length_append] at *
    omega
  · intro i afterHead inside
    have tailBound : i - (logBytes values).length < tail.length := by
      simp only [disk, ← ByteArray.size_data, _root_.List.size_toArray, List.length_map, List.length_append] at inside afterHead
      omega
    have offset : (logBytes values).length + (i - (logBytes values).length) = i := by omega
    have atByte := fresh.2 (i - (logBytes values).length) (by omega)
    rw [← tail_at (logBytes values) tail _ tailBound, offset] at atByte
    simpa only [headSize] using atByte

theorem original_image (values : List U16) (value : U16) :
    AppendImage values value (disk (logBytes values)) := by
  have empty : Fresh value (disk []) := by
    have equal : disk [] = ByteArray.empty := by simp [disk]; rfl
    rw [equal]
    exact fresh_empty value
  simpa using append_fresh_image values value [] empty

/-- The visible full write uses exactly the actual encoder's record layout. -/
theorem complete_write_image (values : List U16) (value : U16) :
    AppendImage values value (overwrite (disk (logBytes values)) (disk (logBytes values)).size
      (bytes (payload value)) 4) := by
  have layoutBytes : bytes (payload value) = disk (layout value).val := by
    simp [bytes, payload, layout, disk, rawByte]
  rw [layoutBytes, Record.TornConcurrent.overwrite_append]
  have complete : ((layout value).val.take 4) = (layout value).val := by simp [layout]
  rw [complete]
  apply append_fresh_image
  simpa [disk, layout, encoded, fourBytes, rawByte] using fresh_encoded value

/-- Every admitted complete-slot image has a concrete ready recovery/repair
script. It returns the acknowledged records, optionally followed by the actual
unacknowledged value, and leaves a synchronized file preserving their prefix. -/
theorem repair_append_image (values : List U16) (value : U16) (image : Image) (rest : Term)
    (maxRecords : Usize) (valid : AppendImage values value image.bytes)
    (fits : (disk (logBytes values)).size + 4 ≤ limit)
    (more : values.length + 1 < maxRecords.val) :
    ∃ recovered : alloc.vec.Vec U16,
      (recovered.val = values ∨ recovered.val = values ++ [value]) ∧
      ∃ script : Term, ∃ final : State,
        repair_log ⟨image.highWater + 1⟩ maxRecords (restarted image script) =
          (.ok (.Ok (some recovered), ⟨image.highWater + 1⟩),
            fileEnv ({} : Environment) ⟨image.highWater + 1⟩ final []) ∧
        final.durable = final.visible ∧ Prefix (disk (logBytes values)) final.durable := by
  obtain ⟨tail, contents, fresh⟩ := append_image_shape values value image.bytes valid
  have length : tail.length ≤ 4 := by simpa [disk, ← ByteArray.size_data] using fresh.1
  have bounded : image.bytes.size ≤ limit := by have size := valid.2.1; omega
  by_cases short : tail.length < 4
  · have shape : LogImage values image.bytes := by rw [contents]; exact log_image values tail short
    refine ⟨alloc.vec.Vec.from values (by scalar_tac), Or.inl (by simp), _, _,
      restart_repair values image rest maxRecords shape bounded (by omega), rfl, ?_⟩
    exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
  · have full : tail.length = 4 := by omega
    let bytes := disk tail
    let a := selected (bytes[0]! != 0) (low value)
    let b := selected (bytes[1]! != 0) (high value)
    let c := selected (bytes[2]! != 0) (low (~~~value))
    let d := selected (bytes[3]! != 0) (high (~~~value))
    have classified : bytes = fourBytes a b c d := by
      have shape := classify_fresh value bytes fresh
      simpa [a, b, c, d, bytes, crop, full, disk, tornBytes, fourBytes, ← ByteArray.size_data] using shape
    have tailList : tail = [a,b,c,d] := by
      have decoded := congrArg (fun bytes : ByteArray => bytes.data.toList.map byteValue) classified
      simpa [bytes, disk, fourBytes, List.map_map, Function.comp_def, byte_roundtrip] using decoded
    rcases torn_decode value (bytes[0]! != 0) (bytes[1]! != 0) (bytes[2]! != 0) (bytes[3]! != 0) with rejected | accepted
    · have bad : word a b ^^^ word c d ≠ core.num.U16.MAX := by
        intro good
        simp [decode_spec, good, a, b, c, d, NativeM.ok] at rejected
      have shape : image.bytes = disk (logBytes values ++ suffixBytes a b c d []) := by
        simpa only [suffixBytes, List.append_nil] using contents.trans (congrArg (fun tail => disk (logBytes values ++ tail)) tailList)
      have bound : (logBytes values ++ suffixBytes a b c d []).length ≤ limit := by
        simpa [shape, disk, ← ByteArray.size_data] using bounded
      refine ⟨alloc.vec.Vec.from values (by scalar_tac), Or.inl (by simp),
        outcome "seek" true 0 (zeroMask image.bytes)
          (planned image.bytes (outcome "set_len" true 0 (zeroMask image.bytes)
            (outcome "sync_all" true 0 ByteArray.empty rest)) (4 * values.length + 4) 0).script,
        malformedRepaired values rest, ?_, rfl, ?_⟩
      · rw [restart_as_fileEnv]
        simpa only [shape] using repair_malformed_default (⟨image.highWater + 1⟩ : NativeFile)
          ({} : Environment) [] values [] a b c d rest 0 maxRecords (by simp [Separate]) bound
          (by simp [limit]) (by omega) bad
      · exact ⟨Nat.le_refl _, fun _ _ => rfl⟩
    · have layout := accepted_layout value a b c d accepted
      have shape : image.bytes = disk (logBytes (values ++ [value])) := by
        rw [contents, tailList, layout]
        simp [logBytes, List.flatMap_append]
      have imageShape : LogImage (values ++ [value]) image.bytes := by
        rw [shape]
        simpa using log_image (values ++ [value]) [] (by decide)
      refine ⟨alloc.vec.Vec.from (values ++ [value]) (by scalar_tac), Or.inr (by simp), _, _,
        restart_repair (values ++ [value]) image rest maxRecords imageShape bounded (by simp; omega), rfl, ?_⟩
      simpa [logBytes, List.flatMap_append] using prefix_append (logBytes values) (Record.IntegrityProperties.layout value).val

end Record.CompleteRecovery
