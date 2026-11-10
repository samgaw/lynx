module
public import StringErrors.Extraction.Funs
public import StringErrors.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace StringErrors.Properties

@[expose] def message (value : U64) : String := "λvalue=" ++ toString value.val

theorem core_preserve_spec {T : Type} (value : T) :
    experiment_core.preserve value = RustM.ok value := by rfl

theorem analysis_preserve_spec {T : Type} (value : T) :
    experiment_analysis.preserve value = RustM.ok value := by
  simpa only [experiment_analysis.preserve] using core_preserve_spec value

theorem text_spec (value : U64)
    (bound : (message value).utf8ByteSize ≤ 4294967295)
    (native : (message value).utf8ByteSize ≤ Isize.max.toNat) :
    experiment_nif.error_text value = RustM.ok (message value) := by
  have program : (Lynx.RustFormatting.Formatting.bytes
      [8#u8, 206#u8, 187#u8, 118#u8, 97#u8, 108#u8, 117#u8, 101#u8, 61#u8, 192#u8, 0#u8]).toList =
      [8, 206, 187, 118, 97, 108, 117, 101, 61, 192, 0] := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[206,187,118,97,108,117,101,61]⟩ = some "λvalue=" := by decide +kernel
  have first : "λvalue=".utf8ByteSize ≤ 4294967295 := by decide +kernel
  simp [experiment_nif.error_text, analysis_preserve_spec, core.hint.must_use, Array.make,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display,
    Lynx.RustFormatting.core.fmt.Arguments.new, Lynx.RustFormatting.alloc.fmt.format,
    U64.Insts.CoreFmtDisplay, Lynx.RustFormatting.core.fmt.num.imp.DisplayU64.fmt,
    program, decoded, Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes,
    Lynx.RustFormatting.Formatting.append, first, message] <;>
    simp_all [message, String.utf8ByteSize_append]

theorem raised_spec (value : U64) (continuation : Bool → Except Lynx.Exception Lynx.Term)
    (bound : (message value).utf8ByteSize ≤ 4294967295)
    (native : (message value).utf8ByteSize ≤ Isize.max.toNat) :
    Lynx.Rustler.Decoding.withDecoded (__RAISED__ value) continuation =
      .error (.error (.bitstring (message value).toUTF8 0)) := by
  simp [__RAISED__, text_spec value bound native, Lynx.Rustler.Decoding.withDecoded_error,
    Lynx.Rustler.raiseTermErrorOutcome, Lynx.Rustler.DecoderError.convert,
    alloc.string.String.Insts.RustlerTypesEncoder, Lynx.Rustler.Encoding.string, bound]

theorem returned_spec (value : U64) (continuation : Bool → Except Lynx.Exception Lynx.Term)
    (bound : (message value).utf8ByteSize ≤ 4294967295)
    (native : (message value).utf8ByteSize ≤ Isize.max.toNat) :
    Lynx.Rustler.Decoding.withDecoded (__RETURNED__ value) continuation =
      .ok (.tuple #[.atom "error", .bitstring (message value).toUTF8 0]) := by
  simp [__RETURNED__, text_spec value bound native, Lynx.Rustler.Decoding.withDecoded_error,
    Lynx.Rustler.termErrorOutcome, Lynx.Rustler.DecoderError.convert,
    alloc.string.String.Insts.RustlerTypesEncoder, Lynx.Rustler.Encoding.string, bound]

private theorem seven_message : message 7#u64 = "λvalue=7" := by
  have repr : toString (7#u64).val = "7" := by
    change Nat.repr 7 = "7"
    have digit : Nat.digitChar 7 = '7' := by
      apply Char.toNat_inj.mp
      exact Nat.toNat_digitChar_of_lt_ten (show 7 < 10 by decide)
    rw [Nat.repr_of_lt (by decide), ← String.toList_inj, String.toList_singleton, digit]
    decide +kernel
  simp only [message, repr]
  decide +kernel

theorem raised_seven (continuation : Bool → Except Lynx.Exception Lynx.Term) :
    Lynx.Rustler.Decoding.withDecoded (__RAISED__ 7#u64) continuation =
      .error (.error (.bitstring "λvalue=7".toUTF8 0)) := by
  have size : (message 7#u64).utf8ByteSize = 9 := by rw [seven_message]; decide +kernel
  have bound : (message 7#u64).utf8ByteSize ≤ 4294967295 := by rw [size]; decide +kernel
  have native : (message 7#u64).utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  have text := seven_message
  simpa only [text] using raised_spec 7#u64 continuation bound native

theorem returned_seven (continuation : Bool → Except Lynx.Exception Lynx.Term) :
    Lynx.Rustler.Decoding.withDecoded (__RETURNED__ 7#u64) continuation =
      .ok (.tuple #[.atom "error", .bitstring "λvalue=7".toUTF8 0]) := by
  have size : (message 7#u64).utf8ByteSize = 9 := by rw [seven_message]; decide +kernel
  have bound : (message 7#u64).utf8ByteSize ≤ 4294967295 := by rw [size]; decide +kernel
  have native : (message 7#u64).utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  have text := seven_message
  simpa only [text] using returned_spec 7#u64 continuation bound native

end StringErrors.Properties
