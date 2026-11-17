module
public import TextSlices.Properties
public section
open Aeneas Aeneas.Std
unseal RustM
namespace TextSlices.Record

@[cbv_eval] theorem tagged_composition (text tag : Str) (length : Usize) :
    experiment_analysis.experiment_core.protocol.tagged_text_field text tag length =
      (do let consumed ← experiment_analysis.text_consume_prefix text tag
          match consumed with
          | none => .ok none
          | some remainder => experiment_analysis.checked_text_split remainder length) := by
  rw [TextSlices.Properties.consume_by_values]
  unfold experiment_analysis.experiment_core.protocol.tagged_text_field
  have consume := TextSlices.Properties.consume_by_values text tag
  change experiment_analysis.experiment_core.protocol.text_consume_prefix text tag = _ at consume
  rw [consume]
  split
  · split <;> simp [Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift,
      experiment_analysis.checked_text_split]
  · simp [Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]

theorem tagged_exact (text tag : Str) (length : Usize)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (tagValid : (TextSlices.Extraction.StringSlices.bytes tag).IsValidUTF8) :
    experiment_analysis.experiment_core.protocol.tagged_text_field text tag length =
      if tag.val.length ≤ text.val.length ∧ tag.val = text.val.take tag.val.length then
        experiment_analysis.checked_text_split (text.drop (Slice.len tag)) length
      else .ok none := by
  rw [tagged_composition, TextSlices.Properties.consume_exact text tag valid tagValid]
  split <;> simp


theorem tagged_returns (text tag : Str) (length : Usize)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (tagValid : (TextSlices.Extraction.StringSlices.bytes tag).IsValidUTF8) :
    ∃ result, experiment_analysis.experiment_core.protocol.tagged_text_field text tag length = .ok result := by
  rw [tagged_exact text tag length valid tagValid]
  split
  · erw [TextSlices.Properties.checked_by_values]
    split <;> exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem tagged_sound (text tag field remainder : Str) (length : Usize)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (tagValid : (TextSlices.Extraction.StringSlices.bytes tag).IsValidUTF8)
    (returned : experiment_analysis.experiment_core.protocol.tagged_text_field text tag length = .ok (some (field, remainder))) :
    tag.val ++ field.val ++ remainder.val = text.val ∧ field.val.length = length.val ∧
    (TextSlices.Extraction.StringSlices.bytes field).IsValidUTF8 ∧
    (TextSlices.Extraction.StringSlices.bytes remainder).IsValidUTF8 := by
  rw [tagged_exact text tag length valid tagValid] at returned
  split at returned
  · rename_i matched
    have consumed : experiment_analysis.text_consume_prefix text tag = .ok (some (text.drop (Slice.len tag))) := by
      rw [TextSlices.Properties.consume_exact text tag valid tagValid]
      rw [if_pos matched]
    have suffixValid := TextSlices.Properties.consume_utf8 text tag _ valid consumed
    have fieldsValid := TextSlices.Properties.checked_utf8 _ field remainder length suffixValid returned
    erw [TextSlices.Properties.checked_by_values] at returned
    split at returned
    · rename_i boundary
      have bounded : length.val ≤ (text.drop (Slice.len tag)).val.length := by
        have position := TextSlices.Extraction.StringSlices.boundary_valid _ suffixValid length boundary
        have bound : length.val ≤ (TextSlices.Extraction.StringSlices.bytes (text.drop (Slice.len tag))).size := by
          simpa [String.Pos.Raw.le_iff, String.rawEndPos, String.utf8ByteSize] using position.le_rawEndPos
        have size := TextSlices.Extraction.StringSlices.size_bytes (text.drop (Slice.len tag))
        simpa only [size] using bound
      have pair := Option.some.inj (RustM.ok_injective returned)
      have left := congrArg Prod.fst pair
      have right := congrArg Prod.snd pair
      dsimp at left right
      subst field remainder
      refine ⟨?_, ?_, fieldsValid⟩
      · simp only [Slice.from_val, Slice.drop, List.take_append_drop, List.append_assoc]
        have splitText := List.take_append_drop tag.val.length text.val
        simpa [← matched.2, Slice.len] using splitText
      · simp only [Slice.from_val, List.length_take, Nat.min_eq_left bounded]
    · simp at returned
  · simp at returned


theorem record_sound (text fieldName value remainder : Str) (nameBytes valueBytes : U8)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8)
    (returned : experiment_analysis.text_record text nameBytes valueBytes = .ok (some (fieldName, value, remainder))) :
    (toStr "name:").val ++ fieldName.val ++ (toStr "|value:").val ++ value.val ++ remainder.val = text.val ∧
    fieldName.val.length = nameBytes.val ∧ value.val.length = valueBytes.val ∧
    (TextSlices.Extraction.StringSlices.bytes fieldName).IsValidUTF8 ∧
    (TextSlices.Extraction.StringSlices.bytes value).IsValidUTF8 ∧
    (TextSlices.Extraction.StringSlices.bytes remainder).IsValidUTF8 := by
  have nameTag : (TextSlices.Extraction.StringSlices.bytes (toStr "name:")).IsValidUTF8 := by cbv; decide +kernel
  have valueTag : (TextSlices.Extraction.StringSlices.bytes (toStr "|value:")).IsValidUTF8 := by cbv; decide +kernel
  obtain ⟨first, firstReturned⟩ := tagged_returns text (toStr "name:") (UScalar.cast .Usize nameBytes) valid nameTag
  unfold experiment_analysis.text_record at returned
  simp only [lift, bind_ok, bind_tc_ok] at returned
  erw [firstReturned] at returned
  simp only [bind_ok, bind_tc_ok, Lynx.Rust.Try.optionBranch] at returned
  cases first with
  | none => simp [Lynx.Rust.Try.optionFromResidual, lift] at returned
  | some pair =>
    rcases pair with ⟨firstName, middle⟩
    dsimp! at returned
    obtain ⟨firstExact, firstSize, firstValid, middleValid⟩ := tagged_sound text (toStr "name:") firstName middle _ valid nameTag firstReturned
    obtain ⟨second, secondReturned⟩ := tagged_returns middle (toStr "|value:") (UScalar.cast .Usize valueBytes) middleValid valueTag
    erw [secondReturned] at returned
    simp only [bind_ok, bind_tc_ok, Lynx.Rust.Try.optionBranch] at returned
    cases second with
    | none => simp [Lynx.Rust.Try.optionFromResidual, lift] at returned
    | some pair =>
      rcases pair with ⟨secondValue, finalRest⟩
      dsimp! at returned
      obtain ⟨secondExact, secondSize, secondValid, finalValid⟩ := tagged_sound middle (toStr "|value:") secondValue finalRest _ middleValid valueTag secondReturned
      have equal : (firstName, secondValue, finalRest) = (fieldName, value, remainder) := by simpa [lift] using returned
      cases equal
      refine ⟨?_, ?_, ?_, firstValid, secondValid, finalValid⟩
      · simpa only [List.append_assoc, secondExact] using firstExact
      · simpa only [U8.cast_Usize_val_eq] using firstSize
      · simpa only [U8.cast_Usize_val_eq] using secondSize

theorem record_accepts (text fieldName middle value remainder : Str) (nameBytes valueBytes : U8)
    (first : experiment_analysis.experiment_core.protocol.tagged_text_field text (toStr "name:")
      (UScalar.cast .Usize nameBytes) = .ok (some (fieldName, middle)))
    (second : experiment_analysis.experiment_core.protocol.tagged_text_field middle (toStr "|value:")
      (UScalar.cast .Usize valueBytes) = .ok (some (value, remainder))) :
    experiment_analysis.text_record text nameBytes valueBytes = .ok (some (fieldName, value, remainder)) := by
  unfold experiment_analysis.text_record
  simp only [lift, bind_ok]
  erw [first]
  simp only [bind_ok, Lynx.Rust.Try.optionBranch]
  dsimp!
  erw [second]
  simp [Lynx.Rust.Try.optionBranch, lift]

theorem record_rejects_first (text : Str) (nameBytes valueBytes : U8)
    (first : experiment_analysis.experiment_core.protocol.tagged_text_field text (toStr "name:")
      (UScalar.cast .Usize nameBytes) = .ok none) :
    experiment_analysis.text_record text nameBytes valueBytes = .ok none := by
  unfold experiment_analysis.text_record
  simp only [lift, bind_ok]
  erw [first]
  simp [Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]

theorem record_rejects_second (text fieldName middle : Str) (nameBytes valueBytes : U8)
    (first : experiment_analysis.experiment_core.protocol.tagged_text_field text (toStr "name:")
      (UScalar.cast .Usize nameBytes) = .ok (some (fieldName, middle)))
    (second : experiment_analysis.experiment_core.protocol.tagged_text_field middle (toStr "|value:")
      (UScalar.cast .Usize valueBytes) = .ok none) :
    experiment_analysis.text_record text nameBytes valueBytes = .ok none := by
  unfold experiment_analysis.text_record
  simp only [lift, bind_ok]
  erw [first]
  simp only [bind_ok, Lynx.Rust.Try.optionBranch]
  dsimp!
  erw [second]
  simp [Lynx.Rust.Try.optionBranch, Lynx.Rust.Try.optionFromResidual, lift]

theorem record_total (text : Str) (nameBytes valueBytes : U8)
    (valid : (TextSlices.Extraction.StringSlices.bytes text).IsValidUTF8) :
    ∃ result, experiment_analysis.text_record text nameBytes valueBytes = .ok result := by
  have nameTag : (TextSlices.Extraction.StringSlices.bytes (toStr "name:")).IsValidUTF8 := by cbv; decide +kernel
  have valueTag : (TextSlices.Extraction.StringSlices.bytes (toStr "|value:")).IsValidUTF8 := by cbv; decide +kernel
  obtain ⟨first, firstReturned⟩ := tagged_returns text (toStr "name:") (UScalar.cast .Usize nameBytes) valid nameTag
  cases first with
  | none => exact ⟨none, record_rejects_first _ _ _ firstReturned⟩
  | some pair =>
    rcases pair with ⟨fieldName, middle⟩
    have middleValid := (tagged_sound text (toStr "name:") fieldName middle _ valid nameTag firstReturned).2.2.2
    obtain ⟨second, secondReturned⟩ := tagged_returns middle (toStr "|value:") (UScalar.cast .Usize valueBytes) middleValid valueTag
    cases second with
    | none => exact ⟨none, record_rejects_second _ _ _ _ _ firstReturned secondReturned⟩
    | some pair =>
      rcases pair with ⟨value, remainder⟩
      exact ⟨some (fieldName, value, remainder), record_accepts _ _ _ _ _ _ _ firstReturned secondReturned⟩

attribute [cbv_eval] bind_ok bind_tc_ok
attribute [local cbv_opaque] RustM.ok RustM.fail

theorem record_unicode :
    experiment_analysis.text_record (toStr "name:é|value:🙂tail") 2#u8 4#u8 =
      .ok (some (toStr "é", toStr "🙂", toStr "tail")) ∧
    experiment_analysis.text_record (toStr "name:|value:") 0#u8 0#u8 =
      .ok (some (toStr "", toStr "", toStr "")) ∧
    experiment_analysis.text_record (toStr "name:é|value:🙂tail") 1#u8 4#u8 = .ok none ∧
    experiment_analysis.text_record (toStr "name:é|wrong:🙂tail") 2#u8 4#u8 = .ok none ∧
    experiment_analysis.text_record (toStr "name:é|value:🙂") 2#u8 5#u8 = .ok none := by
  cbv
  all_goals simp

end TextSlices.Record
