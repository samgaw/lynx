module
public import Derived.Extraction.Funs
public import Derived.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Derived.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem field_success {T : Type} (decoder : Rustler.NativeDecoder T)
    (terms : Slice Term) (position : Str) (index : Usize) (input : Term) (value : T)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (decoded : decoder.decode input = NativeM.ok (.Ok value)) :
    derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index
      decoder terms position index = NativeM.ok (.Ok value) := by
  simp [derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
    indexed, decoded, NativeM.lift, NativeM.ok]

theorem decoder_success (expected replacement : U64) :
    derived.Request.Insts.RustlerTypesDecoder.decode
      (.tuple #[Rustler.encodeUnsigned expected, Rustler.encodeUnsigned replacement]) =
      NativeM.ok (.Ok {expected, replacement}) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have decoded (value : U64) : Rustler.NativeDecoding.u64 (Rustler.encodeUnsigned value) =
      NativeM.ok (.Ok value) := by
    have valid := Rustler.decodeUnsigned_encodeUnsigned value
    change Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned value) = .ok value at valid
    simp [Rustler.NativeDecoding.u64, Rustler.Decoding.u64, valid,
      NativeM.lift, NativeM.fromRust, NativeM.ok]
  simp [derived.Request.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref,
    derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
    Slice.index_usize, U64.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem non_tuple (input : Term) (notTuple : ∀ fields, input ≠ .tuple fields) :
    derived.Request.Insts.RustlerTypesDecoder.decode input =
      NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp [derived.Request.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple_not_tuple input notTuple,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem arity_rejected (fields : Array Term) (wrong : fields.size ≠ 2)
    (bounds : fields.toList.length ≤ Usize.max ∧ fields.toList.length ≤ Isize.max.toNat ∧
      fields.toList.length ≤ 16777215) :
    derived.Request.Insts.RustlerTypesDecoder.decode (.tuple fields) =
      NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp only [Array.length_toList] at bounds
  simp [derived.Request.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.lift, NativeM.fromRust, NativeM.ok, wrong]

theorem oversized (fields : Array Term) (large : 16777215 < fields.size) :
    derived.Request.Insts.RustlerTypesDecoder.decode (.tuple fields) = .error .exhausted := by
  have bounds : ¬ (fields.toList.length ≤ Usize.max ∧ fields.toList.length ≤ Isize.max.toNat ∧
      fields.toList.length ≤ 16777215) := by simp only [Array.length_toList]; omega
  simp [derived.Request.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple_exhausted fields bounds,
    NativeM.lift, NativeM.fromRust]

theorem field_expected_error (terms : Slice Lynx.Term) (index : Usize) (input : Lynx.Term)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (rejected : Lynx.Rustler.NativeDecoding.u64 input = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    atomic_nif.derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index
      atomic_nif.U64.Insts.RustlerTypesDecoder terms (toStr "expected") index =
      NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field expected on Request"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [23#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 192#u8, 11#u8, 32#u8, 111#u8, 110#u8, 32#u8, 82#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8, 0#u8]).toList = [23, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 192, 11, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32]⟩ = some "Could not decode field " := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ = some " on Request" := by decide +kernel
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "expected").val).toList = [101, 120, 112, 101, 99, 116, 101, 100] := by decide +kernel
  have decodedField : String.fromUTF8? ⟨#[101, 120, 112, 101, 99, 116, 101, 100]⟩ = some "expected" := by decide +kernel
  simp [atomic_nif.derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
    NativeM.lift, NativeM.fromRust, NativeM.ok, indexed, rejected, atomic_nif.U64.Insts.RustlerTypesDecoder,
    atomic_nif.Shared0T.Insts.CoreFmtDisplay, atomic_nif.Str.Insts.CoreFmtDisplay,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display,
    Lynx.RustFormatting.core.fmt.DisplayShared.fmt, Lynx.RustFormatting.core.fmt.DisplayStr.fmt,
    Lynx.RustFormatting.core.fmt.Formatter.write_str,
    Lynx.RustFormatting.core.fmt.Arguments.new, Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format, Lynx.RustFormatting.Formatting.run,
    Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append,
    Array.make, atomic_nif.core.hint.must_use, program, decodedPrefix,
    decodedSuffix, fieldBytes, decodedField, Lynx.Rustler.Decoding.dropDecoderError,
    Lynx.Rustler.badArgOutcome]
  have first : "Could not decode field ".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field " ++ "expected" ++ " on Request" = "Could not decode field expected on Request" := by decide +kernel
  have middleSize : "Could not decode field expected".utf8ByteSize = 31 := by decide +kernel
  have fieldSize : "expected".utf8ByteSize = 8 := by decide +kernel
  have prefixSize : "Could not decode field ".utf8ByteSize = 23 := by decide +kernel
  have suffixSize : " on Request".utf8ByteSize = 11 := by decide +kernel
  have size : "Could not decode field expected on Request".utf8ByteSize = 42 := by decide +kernel
  have machine : "Could not decode field expected on Request".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp_all [String.utf8ByteSize_append, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem field_replacement_error (terms : Slice Lynx.Term) (index : Usize) (input : Lynx.Term)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (rejected : Lynx.Rustler.NativeDecoding.u64 input = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    atomic_nif.derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index
      atomic_nif.U64.Insts.RustlerTypesDecoder terms (toStr "replacement") index =
      NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field replacement on Request"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [23#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 192#u8, 11#u8, 32#u8, 111#u8, 110#u8, 32#u8, 82#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8, 0#u8]).toList = [23, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 192, 11, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32]⟩ = some "Could not decode field " := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ = some " on Request" := by decide +kernel
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "replacement").val).toList = [114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116] := by decide +kernel
  have decodedField : String.fromUTF8? ⟨#[114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116]⟩ = some "replacement" := by decide +kernel
  simp [atomic_nif.derived.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
    NativeM.lift, NativeM.fromRust, NativeM.ok, indexed, rejected, atomic_nif.U64.Insts.RustlerTypesDecoder,
    atomic_nif.Shared0T.Insts.CoreFmtDisplay, atomic_nif.Str.Insts.CoreFmtDisplay,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_display,
    Lynx.RustFormatting.core.fmt.DisplayShared.fmt, Lynx.RustFormatting.core.fmt.DisplayStr.fmt,
    Lynx.RustFormatting.core.fmt.Formatter.write_str,
    Lynx.RustFormatting.core.fmt.Arguments.new, Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format, Lynx.RustFormatting.Formatting.run,
    Lynx.RustFormatting.Formatting.writeBytes, Lynx.RustFormatting.Formatting.append,
    Array.make, atomic_nif.core.hint.must_use, program, decodedPrefix,
    decodedSuffix, fieldBytes, decodedField, Lynx.Rustler.Decoding.dropDecoderError,
    Lynx.Rustler.badArgOutcome]
  have first : "Could not decode field ".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field " ++ "replacement" ++ " on Request" = "Could not decode field replacement on Request" := by decide +kernel
  have middleSize : "Could not decode field replacement".utf8ByteSize = 34 := by decide +kernel
  have fieldSize : "replacement".utf8ByteSize = 11 := by decide +kernel
  have prefixSize : "Could not decode field ".utf8ByteSize = 23 := by decide +kernel
  have suffixSize : " on Request".utf8ByteSize = 11 := by decide +kernel
  have size : "Could not decode field replacement on Request".utf8ByteSize = 45 := by decide +kernel
  have machine : "Could not decode field replacement on Request".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp_all [String.utf8ByteSize_append, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem decoder_expected_error (bad replacement : Lynx.Term)
    (rejected : Lynx.Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.tuple #[bad, replacement]) =
      NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
          "Could not decode field expected on Request"⟩)) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  let terms := alloc.vec.Vec.deref (alloc.vec.Vec.from [bad, replacement] bounds.1)
  have indexed : Slice.index_usize terms 0#usize = RustM.ok bad := by
    simp [terms, alloc.vec.Vec.deref, Slice.index_usize]
  have failed := field_expected_error terms 0#usize bad indexed rejected
  simp [atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode,
    NativeM.lift, NativeM.fromRust, NativeM.ok, Lynx.Rustler.NativeDecoding.getTuple,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.len,
    core.result.Result.Insts.CoreOpsTry.branch, failed,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, terms]

theorem decoder_replacement_error (expected : U64) (bad : Lynx.Term)
    (rejected : Lynx.Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode
      (.tuple #[Lynx.Rustler.encodeUnsigned expected, bad]) =
      NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
          "Could not decode field replacement on Request"⟩)) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  let terms := alloc.vec.Vec.deref (alloc.vec.Vec.from [Lynx.Rustler.encodeUnsigned expected, bad] bounds.1)
  have indexedLow : Slice.index_usize terms 0#usize = RustM.ok (Lynx.Rustler.encodeUnsigned expected) := by
    simp [terms, alloc.vec.Vec.deref, Slice.index_usize]
  have indexedHigh : Slice.index_usize terms 1#usize = RustM.ok bad := by
    simp [terms, alloc.vec.Vec.deref, Slice.index_usize]
  have decoded : atomic_nif.U64.Insts.RustlerTypesDecoder.decode (Lynx.Rustler.encodeUnsigned expected) = NativeM.ok (.Ok expected) := by
    have valid := Lynx.Rustler.decodeUnsigned_encodeUnsigned expected
    change Lynx.Rustler.decodeUnsigned .U64 64 (Lynx.Rustler.encodeUnsigned expected) = .ok expected at valid
    simp [Lynx.Rustler.NativeDecoding.u64, Lynx.Rustler.Decoding.u64, valid, NativeM.lift, NativeM.fromRust, NativeM.ok]
  have first := field_success atomic_nif.U64.Insts.RustlerTypesDecoder terms (toStr "expected")
    0#usize (Lynx.Rustler.encodeUnsigned expected) expected indexedLow decoded
  have failed := field_replacement_error terms 1#usize bad indexedHigh rejected
  simp [atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode,
    NativeM.lift, NativeM.fromRust, NativeM.ok, Lynx.Rustler.NativeDecoding.getTuple,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.len,
    core.result.Result.Insts.CoreOpsTry.branch, first, failed,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, terms]

theorem contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_core.replace counter expected replacement =
      NativeAtomic.compareExchange counter expected replacement .SeqCst .SeqCst := by rfl

theorem composed (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_analysis.try_set counter expected replacement = (do
      let result ← atomic_core.replace counter expected replacement
      match result with
      | .Ok previous => NativeM.ok (true, previous)
      | .Err observed => NativeM.ok (false, observed)) := by rfl

theorem resource_contract (owner : NativeResourceArc Counter) (request : derived.Request) :
    derived.counter_tuple owner request = (do
      let counter ← NativeResourceArc.deref owner
      let result ← atomic_analysis.try_set counter.state request.expected request.replacement
      NativeOwnedDrop.drop owner
      NativeM.ok result) := by rfl

theorem reference_eq (left right : Nat) :
    (Term.nativeReference left == Term.nativeReference right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]
  simp

@[expose] def retained (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := [
      (4,NativeResourceArc.handleType Counter,.nativeReference 2),
      (3,NativeResourceArc.handleType Counter,.nativeReference 2),
      (2,NativeResourceArc.typeName Counter,
        .tuple #[.integer 2,NativeCodec.encode ({state := ⟨1⟩} : Counter)]),
      (1,NativeAtomic.typeName,NativeCodec.encode value)] }

@[expose] def afterCall (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := [
      (4,NativeResourceArc.handleType Counter,.nativeReference 2),
      (2,NativeResourceArc.typeName Counter,
        .tuple #[.integer 1,NativeCodec.encode ({state := ⟨1⟩} : Counter)]),
      (1,NativeAtomic.typeName,NativeCodec.encode value)] }

theorem matched (previous replacement : U64) (schedule : List ScheduleChoice) :
    (derived.counter_tuple ⟨2,3⟩ {expected := previous, replacement}).run (retained previous) schedule =
      (.ok (true,previous), afterCall replacement) := by
  simp [resource_contract, composed, contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem mismatch (previous expected replacement : U64) (different : previous ≠ expected)
    (schedule : List ScheduleChoice) :
    (derived.counter_tuple ⟨2,3⟩ {expected, replacement}).run (retained previous) schedule =
      (.ok (false,previous), afterCall previous) := by
  simp [resource_contract, composed, contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, different, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide
end Derived.Properties
