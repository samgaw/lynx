module
public import Scalars.Extraction.Funs
public import Scalars.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Scalars.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem bool_decoded (input : Term) (value : Bool)
    (decoded : Rustler.NativeDecoding.bool input = NativeM.ok (.Ok value)) :
    scalars.BoolValue.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.BoolValue.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeBoolValue.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    Bool.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem i8_decoded (input : Term) (value : I8)
    (decoded : Rustler.NativeDecoding.i8 input = NativeM.ok (.Ok value)) :
    scalars.I8Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.I8Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeI8Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    I8.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem i16_decoded (input : Term) (value : I16)
    (decoded : Rustler.NativeDecoding.i16 input = NativeM.ok (.Ok value)) :
    scalars.I16Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.I16Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeI16Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    I16.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem i32_decoded (input : Term) (value : I32)
    (decoded : Rustler.NativeDecoding.i32 input = NativeM.ok (.Ok value)) :
    scalars.I32Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.I32Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeI32Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    I32.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem i64_decoded (input : Term) (value : I64)
    (decoded : Rustler.NativeDecoding.i64 input = NativeM.ok (.Ok value)) :
    scalars.I64Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.I64Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeI64Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    I64.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem u8_decoded (input : Term) (value : U8)
    (decoded : Rustler.NativeDecoding.u8 input = NativeM.ok (.Ok value)) :
    scalars.U8Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.U8Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeU8Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    U8.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem u16_decoded (input : Term) (value : U16)
    (decoded : Rustler.NativeDecoding.u16 input = NativeM.ok (.Ok value)) :
    scalars.U16Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.U16Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeU16Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    U16.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem u32_decoded (input : Term) (value : U32)
    (decoded : Rustler.NativeDecoding.u32 input = NativeM.ok (.Ok value)) :
    scalars.U32Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.U32Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeU32Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    U32.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem u64_decoded (input : Term) (value : U64)
    (decoded : Rustler.NativeDecoding.u64 input = NativeM.ok (.Ok value)) :
    scalars.U64Value.Insts.RustlerTypesDecoder.decode (.tuple #[input]) =
      NativeM.ok (.Ok {value}) := by
  have bounds : (1 : Nat) ≤ Usize.max ∧ 1 ≤ Isize.max.toNat ∧ 1 ≤ 16777215 := by scalar_tac
  simp [scalars.U64Value.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeU64Value.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    U64.Insts.RustlerTypesDecoder, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem request_decoded (enabled : Bool) (signed unsigned : Term) (left : I8) (right : U16)
    (signedDecoded : Rustler.NativeDecoding.i8 signed = NativeM.ok (.Ok left))
    (unsignedDecoded : Rustler.NativeDecoding.u16 unsigned = NativeM.ok (.Ok right)) :
    scalars.Request.Insts.RustlerTypesDecoder.decode
      (.tuple #[Rustler.encodeBool enabled, signed, unsigned]) =
      NativeM.ok (.Ok {enabled, signed := left, unsigned := right}) := by
  have bounds : (3 : Nat) ≤ Usize.max ∧ 3 ≤ Isize.max.toNat ∧ 3 ≤ 16777215 := by scalar_tac
  have boolean : Rustler.NativeDecoding.bool (Rustler.encodeBool enabled) = NativeM.ok (.Ok enabled) := by
    simp [Rustler.NativeDecoding.bool, Rustler.Decoding.bool,
      Rustler.decodeBool_encodeBool, NativeM.lift, NativeM.fromRust, NativeM.ok]
  simp [scalars.Request.Insts.RustlerTypesDecoder.decode,
    scalars.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    Bool.Insts.RustlerTypesDecoder, I8.Insts.RustlerTypesDecoder, U16.Insts.RustlerTypesDecoder,
    boolean, signedDecoded, unsignedDecoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem i8_narrows : scalars.I8Value.Insts.RustlerTypesDecoder.decode
    (.tuple #[.integer 255]) = NativeM.ok (.Ok {value := (-1)#i8}) := by
  apply i8_decoded
  rfl

theorem i16_narrows : scalars.I16Value.Insts.RustlerTypesDecoder.decode
    (.tuple #[.integer 65535]) = NativeM.ok (.Ok {value := (-1)#i16}) := by
  apply i16_decoded
  rfl

theorem u8_narrows : scalars.U8Value.Insts.RustlerTypesDecoder.decode
    (.tuple #[.integer 256]) = NativeM.ok (.Ok {value := 0#u8}) := by
  apply u8_decoded
  rfl

theorem u16_narrows : scalars.U16Value.Insts.RustlerTypesDecoder.decode
    (.tuple #[.integer 65537]) = NativeM.ok (.Ok {value := 1#u16}) := by
  apply u16_decoded
  rfl

theorem contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_core.replace counter expected replacement =
      NativeAtomic.compareExchange counter expected replacement .SeqCst .SeqCst := by rfl

theorem composed (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_analysis.try_set counter expected replacement = (do
      let result ← atomic_core.replace counter expected replacement
      match result with
      | .Ok previous => NativeM.ok (true, previous)
      | .Err observed => NativeM.ok (false, observed)) := by rfl

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

theorem current_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_core.current counter = NativeAtomic.load counter .SeqCst := by rfl

theorem updated (signed : I8) (unsigned : U16) (allowed : 0#i8 ≤ signed)
    (schedule : List ScheduleChoice) :
    (scalars.counter_scalar ⟨2,3⟩ {enabled := true, signed, unsigned}).run
      (retained 0#u64) schedule =
      (.ok (signed, unsigned, true, 0#u64), afterCall (core.convert.num.FromU64U16.from unsigned)) := by
  simp [scalars.counter_scalar, composed, contract, current_contract, retained, afterCall,
    allowed,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.load,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem disabled (previous : U64) (signed : I8) (unsigned : U16)
    (schedule : List ScheduleChoice) :
    (scalars.counter_scalar ⟨2,3⟩ {enabled := false, signed, unsigned}).run
      (retained previous) schedule =
      (.ok (signed, unsigned, false, previous), afterCall (previous)) := by
  simp [scalars.counter_scalar, composed, contract, current_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.load,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem negative (previous : U64) (signed : I8) (unsigned : U16) (negative : signed < 0#i8)
    (schedule : List ScheduleChoice) :
    (scalars.counter_scalar ⟨2,3⟩ {enabled := true, signed, unsigned}).run
      (retained previous) schedule =
      (.ok (signed, unsigned, false, previous), afterCall (previous)) := by
  simp [scalars.counter_scalar, composed, contract, current_contract, retained, afterCall,
    show ¬ 0#i8 ≤ signed from not_le.mpr negative,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.load,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem signed_field_error (terms : Slice Lynx.Term) (index : Usize) (input : Lynx.Term)
    (indexed : Slice.index_usize terms index = RustM.ok input)
    (rejected : Lynx.Rustler.NativeDecoding.i8 input = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    atomic_nif.scalars.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index
      atomic_nif.I8.Insts.RustlerTypesDecoder terms (toStr "signed") index =
      NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field signed on Request"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [23#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 192#u8, 11#u8, 32#u8, 111#u8, 110#u8, 32#u8, 82#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8, 0#u8]).toList = [23, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 192, 11, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32]⟩ = some "Could not decode field " := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ = some " on Request" := by decide +kernel
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "signed").val).toList = [115, 105, 103, 110, 101, 100] := by decide +kernel
  have decodedField : String.fromUTF8? ⟨#[115, 105, 103, 110, 101, 100]⟩ = some "signed" := by decide +kernel
  simp [atomic_nif.scalars.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
    NativeM.lift, NativeM.fromRust, NativeM.ok, indexed, rejected, atomic_nif.I8.Insts.RustlerTypesDecoder,
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
  have joined : "Could not decode field " ++ "signed" ++ " on Request" = "Could not decode field signed on Request" := by decide +kernel
  have middleSize : "Could not decode field signed".utf8ByteSize = 29 := by decide +kernel
  have fieldSize : "signed".utf8ByteSize = 6 := by decide +kernel
  have prefixSize : "Could not decode field ".utf8ByteSize = 23 := by decide +kernel
  have suffixSize : " on Request".utf8ByteSize = 11 := by decide +kernel
  have size : "Could not decode field signed on Request".utf8ByteSize = 40 := by decide +kernel
  have machine : "Could not decode field signed on Request".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp_all [String.utf8ByteSize_append, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem request_signed_error (enabled : Bool) (bad unsigned : Term)
    (rejected : Rustler.NativeDecoding.i8 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    scalars.Request.Insts.RustlerTypesDecoder.decode
      (.tuple #[Rustler.encodeBool enabled, bad, unsigned]) =
      NativeM.ok (.Err (Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
          "Could not decode field signed on Request"⟩)) := by
  have bounds : (3 : Nat) ≤ Usize.max ∧ 3 ≤ Isize.max.toNat ∧ 3 ≤ 16777215 := by scalar_tac
  have boolean : Rustler.NativeDecoding.bool (Rustler.encodeBool enabled) = NativeM.ok (.Ok enabled) := by
    simp [Rustler.NativeDecoding.bool, Rustler.Decoding.bool,
      Rustler.decodeBool_encodeBool, NativeM.lift, NativeM.fromRust, NativeM.ok]
  have field : scalars.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index
      I8.Insts.RustlerTypesDecoder
      (Slice.from [Rustler.encodeBool enabled, bad, unsigned] (by scalar_tac))
      (toStr "signed") 1#usize = NativeM.ok (.Err (Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
          "Could not decode field signed on Request"⟩)) := by
    apply signed_field_error _ _ bad _ rejected
    simp [Slice.index_usize]
  have first : scalars.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index
      Bool.Insts.RustlerTypesDecoder
      (Slice.from [Rustler.encodeBool enabled, bad, unsigned] (by scalar_tac))
      (toStr "enabled") 0#usize = NativeM.ok (.Ok enabled) := by
    simp [scalars.Decoder__rustler_decode_lifetimeRequest.decode.try_decode_index,
      Bool.Insts.RustlerTypesDecoder, Slice.index_usize, boolean, NativeM.lift, NativeM.ok]
  simp [scalars.Request.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    Bool.Insts.RustlerTypesDecoder, boolean,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, field, first,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem request_signed_encoded (enabled : Bool) (bad unsigned : Term)
    (rejected : Rustler.NativeDecoding.i8 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    scalars.Request.Insts.RustlerTypesDecoder.decode
      (.tuple #[Rustler.encodeBool enabled, bad, unsigned]) =
      NativeM.ok (.Err (.encoded true (fun _ => RustM.ok
        (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 115, 105, 103, 110, 101, 100, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0)))) := by
  have size : "Could not decode field signed on Request".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have encoded (env : Rustler.Env) : Rustler.Encoding.string "Could not decode field signed on Request" env =
      RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 115, 105, 103, 110, 101, 100, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0) := by
    simp [Rustler.Encoding.string, size]
    decide +kernel
  simpa only [Rustler.raiseTermErrorOutcome,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, encoded] using
    request_signed_error enabled bad unsigned rejected

end Scalars.Properties
