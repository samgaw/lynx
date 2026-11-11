module
public import RustWorkspace.TupleDecodeFacade.Funs
public import RustWorkspace.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.DerivedTupleDecoder

theorem core_spec (left right : U64) :
    experiment_nif.experiment_core.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := by
  unfold experiment_nif.experiment_core.order_pair
  split <;> rfl

theorem caller_spec (left right : U64) :
    experiment_nif.experiment_analysis.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := core_spec left right

theorem ordered_fields (left right : U64) :
    ∃ low high, experiment_nif.experiment_analysis.order_pair left right = RustM.ok (low, high) ∧
      low.val ≤ high.val ∧ ((low = left ∧ high = right) ∨ (low = right ∧ high = left)) := by
  by_cases h : left ≤ right
  · refine ⟨left, right, ?_, ?_, Or.inl ⟨rfl, rfl⟩⟩
    · simp [caller_spec, h]
    · exact h
  · refine ⟨right, left, ?_, ?_, Or.inr ⟨rfl, rfl⟩⟩
    · simp [caller_spec, h]
    · change ¬ left.val ≤ right.val at h
      omega

theorem facade_spec (value : experiment_nif.OrderedFields) :
    experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.ordered_tuple value =
      RustM.ok (if value.low ≤ value.high then value else {low := value.high, high := value.low}) := by
  cases value with
  | mk low high =>
    by_cases ordered : low ≤ high <;>
      simp [experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.ordered_tuple,
        caller_spec, ordered]

theorem encoder_spec (value : experiment_nif.OrderedFields) (env : Lynx.Rustler.Env) :
    experiment_nif.OrderedFields.Insts.RustlerTypesEncoder.encode value env =
      RustM.ok (.tuple #[.integer value.low.val, .integer value.high.val]) := by
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesEncoder.encode,
    Lynx.Rustler.Encoding.u64, Lynx.Rustler.Encoding.makeTuple,
    Array.to_slice, Array.make, lift]

theorem field_success {T : Type} (decoder : Lynx.Rustler.Decoder T)
    (terms : Slice Lynx.Term) (position : Str) (index : Usize) (input : Lynx.Term) (value : T)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (decoded : decoder.decode input = RustM.ok (.Ok value)) :
    experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index
      decoder terms position index = RustM.ok (.Ok value) := by
  simp [experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index,
    indexed, decoded]

theorem decoder_success (low high : U64) :
    experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode
      (.tuple #[Lynx.Rustler.encodeUnsigned low, Lynx.Rustler.encodeUnsigned high]) =
      RustM.ok (.Ok {low, high}) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have decoded (v : U64) : Lynx.Rustler.Decoding.u64 (Lynx.Rustler.encodeUnsigned v) = RustM.ok (.Ok v) := by
    have valid := Lynx.Rustler.decodeUnsigned_encodeUnsigned v
    change Lynx.Rustler.decodeUnsigned .U64 64 (Lynx.Rustler.encodeUnsigned v) = .ok v at valid
    simp [Lynx.Rustler.Decoding.u64, valid]
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.len, alloc.vec.Vec.deref,
    experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index,
    Slice.index_usize, experiment_nif.U64.Insts.RustlerTypesDecoder,
    decoded, core.result.Result.Insts.CoreOpsTry.branch]

theorem non_tuple (input : Lynx.Term) (notTuple : ∀ fields, input ≠ .tuple fields) :
    experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode input =
      RustM.ok (.Err Lynx.Rustler.badArgOutcome) := by
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode,
    Lynx.Rustler.Decoding.getTuple_not_tuple input notTuple,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame]

theorem arity_rejected (fields : Array Lynx.Term)
    (bounds : fields.toList.length ≤ Usize.max ∧ fields.toList.length ≤ Isize.max.toNat ∧ fields.toList.length ≤ 16777215)
    (wrong : fields.toList.length ≠ 2) :
    experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode (.tuple fields) =
      RustM.ok (.Err Lynx.Rustler.badArgOutcome) := by
  have wrongSize : fields.size ≠ 2 := by simpa using wrong
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode,
    Lynx.Rustler.Decoding.getTuple_fields fields bounds,
    core.result.Result.Insts.CoreOpsTry.branch, wrongSize]

theorem oversized (fields : Array Lynx.Term)
    (outside : ¬ (fields.toList.length ≤ Usize.max ∧ fields.toList.length ≤ Isize.max.toNat ∧ fields.toList.length ≤ 16777215)) :
    experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode (.tuple fields) =
      RustM.fail .undef := by
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode,
    Lynx.Rustler.Decoding.getTuple_exhausted fields outside]

theorem field_low_error (terms : Slice Lynx.Term) (index : Usize) (input : Lynx.Term)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (rejected : Lynx.Rustler.Decoding.u64 input = RustM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index
      experiment_nif.U64.Insts.RustlerTypesDecoder terms (toStr "low") index =
      RustM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, experiment_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field low on OrderedFields"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [23#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 192#u8, 17#u8, 32#u8, 111#u8, 110#u8, 32#u8, 79#u8, 114#u8, 100#u8, 101#u8, 114#u8, 101#u8, 100#u8, 70#u8, 105#u8, 101#u8, 108#u8, 100#u8, 115#u8, 0#u8]).toList = [23, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 192, 17, 32, 111, 110, 32, 79, 114, 100, 101, 114, 101, 100, 70, 105, 101, 108, 100, 115, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32]⟩ = some "Could not decode field " := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 79, 114, 100, 101, 114, 101, 100, 70, 105, 101, 108, 100, 115]⟩ = some " on OrderedFields" := by decide +kernel
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "low").val).toList = [108, 111, 119] := by decide +kernel
  have decodedField : String.fromUTF8? ⟨#[108, 111, 119]⟩ = some "low" := by decide +kernel
  simp [experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index,
    indexed, rejected, experiment_nif.U64.Insts.RustlerTypesDecoder,
    experiment_nif.Shared0T.Insts.CoreFmtDisplay, experiment_nif.Str.Insts.CoreFmtDisplay,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display,
    Lynx.RustFormatting.core.fmt.DisplayShared.fmt, Lynx.RustFormatting.core.fmt.DisplayStr.fmt,
    Lynx.RustFormatting.core.fmt.Formatter.write_str,
    Lynx.RustFormatting.core.fmt.Arguments.new, Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format, Lynx.RustFormatting.Formatting.run,
    Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append,
    Array.make, experiment_nif.core.hint.must_use, program, decodedPrefix,
    decodedSuffix, fieldBytes, decodedField, Lynx.Rustler.Decoding.dropDecoderError,
    Lynx.Rustler.badArgOutcome]
  have first : "Could not decode field ".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field " ++ "low" ++ " on OrderedFields" = "Could not decode field low on OrderedFields" := by decide +kernel
  have middleSize : "Could not decode field low".utf8ByteSize = 26 := by decide +kernel
  have fieldSize : "low".utf8ByteSize = 3 := by decide +kernel
  have prefixSize : "Could not decode field ".utf8ByteSize = 23 := by decide +kernel
  have suffixSize : " on OrderedFields".utf8ByteSize = 17 := by decide +kernel
  have size : "Could not decode field low on OrderedFields".utf8ByteSize = 43 := by decide +kernel
  have machine : "Could not decode field low on OrderedFields".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp_all [String.utf8ByteSize_append]

theorem field_high_error (terms : Slice Lynx.Term) (index : Usize) (input : Lynx.Term)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (rejected : Lynx.Rustler.Decoding.u64 input = RustM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index
      experiment_nif.U64.Insts.RustlerTypesDecoder terms (toStr "high") index =
      RustM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, experiment_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field high on OrderedFields"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [23#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 192#u8, 17#u8, 32#u8, 111#u8, 110#u8, 32#u8, 79#u8, 114#u8, 100#u8, 101#u8, 114#u8, 101#u8, 100#u8, 70#u8, 105#u8, 101#u8, 108#u8, 100#u8, 115#u8, 0#u8]).toList = [23, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 192, 17, 32, 111, 110, 32, 79, 114, 100, 101, 114, 101, 100, 70, 105, 101, 108, 100, 115, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32]⟩ = some "Could not decode field " := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 79, 114, 100, 101, 114, 101, 100, 70, 105, 101, 108, 100, 115]⟩ = some " on OrderedFields" := by decide +kernel
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "high").val).toList = [104, 105, 103, 104] := by decide +kernel
  have decodedField : String.fromUTF8? ⟨#[104, 105, 103, 104]⟩ = some "high" := by decide +kernel
  simp [experiment_nif.Decoder__rustler_decode_lifetimeOrderedFields.decode.try_decode_index,
    indexed, rejected, experiment_nif.U64.Insts.RustlerTypesDecoder,
    experiment_nif.Shared0T.Insts.CoreFmtDisplay, experiment_nif.Str.Insts.CoreFmtDisplay,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display,
    Lynx.RustFormatting.core.fmt.DisplayShared.fmt, Lynx.RustFormatting.core.fmt.DisplayStr.fmt,
    Lynx.RustFormatting.core.fmt.Formatter.write_str,
    Lynx.RustFormatting.core.fmt.Arguments.new, Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format, Lynx.RustFormatting.Formatting.run,
    Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append,
    Array.make, experiment_nif.core.hint.must_use, program, decodedPrefix,
    decodedSuffix, fieldBytes, decodedField, Lynx.Rustler.Decoding.dropDecoderError,
    Lynx.Rustler.badArgOutcome]
  have first : "Could not decode field ".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field " ++ "high" ++ " on OrderedFields" = "Could not decode field high on OrderedFields" := by decide +kernel
  have middleSize : "Could not decode field high".utf8ByteSize = 27 := by decide +kernel
  have fieldSize : "high".utf8ByteSize = 4 := by decide +kernel
  have prefixSize : "Could not decode field ".utf8ByteSize = 23 := by decide +kernel
  have suffixSize : " on OrderedFields".utf8ByteSize = 17 := by decide +kernel
  have size : "Could not decode field high on OrderedFields".utf8ByteSize = 44 := by decide +kernel
  have machine : "Could not decode field high on OrderedFields".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp_all [String.utf8ByteSize_append]

theorem decoder_low_error (bad high : Lynx.Term)
    (rejected : Lynx.Rustler.Decoding.u64 bad = RustM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode (.tuple #[bad, high]) =
      RustM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, experiment_nif.alloc.string.String.Insts.RustlerTypesEncoder,
          "Could not decode field low on OrderedFields"⟩)) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  let terms := alloc.vec.Vec.deref (alloc.vec.Vec.from [bad, high] bounds.1)
  have indexed : Slice.index_usize terms 0#usize = RustM.ok bad := by
    simp [terms, alloc.vec.Vec.deref, Slice.index_usize]
  have failed := field_low_error terms 0#usize bad indexed rejected
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.len,
    core.result.Result.Insts.CoreOpsTry.branch, failed,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, terms]

theorem decoder_high_error (low : U64) (bad : Lynx.Term)
    (rejected : Lynx.Rustler.Decoding.u64 bad = RustM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode
      (.tuple #[Lynx.Rustler.encodeUnsigned low, bad]) =
      RustM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, experiment_nif.alloc.string.String.Insts.RustlerTypesEncoder,
          "Could not decode field high on OrderedFields"⟩)) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  let terms := alloc.vec.Vec.deref (alloc.vec.Vec.from [Lynx.Rustler.encodeUnsigned low, bad] bounds.1)
  have indexedLow : Slice.index_usize terms 0#usize = RustM.ok (Lynx.Rustler.encodeUnsigned low) := by
    simp [terms, alloc.vec.Vec.deref, Slice.index_usize]
  have indexedHigh : Slice.index_usize terms 1#usize = RustM.ok bad := by
    simp [terms, alloc.vec.Vec.deref, Slice.index_usize]
  have decoded : experiment_nif.U64.Insts.RustlerTypesDecoder.decode (Lynx.Rustler.encodeUnsigned low) = RustM.ok (.Ok low) := by
    have valid := Lynx.Rustler.decodeUnsigned_encodeUnsigned low
    change Lynx.Rustler.decodeUnsigned .U64 64 (Lynx.Rustler.encodeUnsigned low) = .ok low at valid
    simp [Lynx.Rustler.Decoding.u64, valid]
  have first := field_success experiment_nif.U64.Insts.RustlerTypesDecoder terms (toStr "low")
    0#usize (Lynx.Rustler.encodeUnsigned low) low indexedLow decoded
  have failed := field_high_error terms 1#usize bad indexedHigh rejected
  simp [experiment_nif.OrderedFields.Insts.RustlerTypesDecoder.decode,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.len,
    core.result.Result.Insts.CoreOpsTry.branch, first, failed,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, terms]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.TupleDecodeFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.NativeFormatting
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedTupleDecoder
end RustWorkspace.DerivedTupleDecoder
