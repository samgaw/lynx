module
public import TaggedDecode.Extraction.Funs
public import TaggedDecode.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace TaggedDecode.Properties

@[expose] def replyTerm : OrderedReply → Lynx.Term
  | .Empty => .atom "empty"
  | .Equal value => .tuple #[Lynx.Term.atom "equal", Lynx.Rustler.encodeUnsigned value]
  | .Ordered left right => .tuple #[Lynx.Term.atom "ordered", Lynx.Rustler.encodeUnsigned left, Lynx.Rustler.encodeUnsigned right]

theorem decode_u64 (value : U64) :
    Lynx.Rustler.Decoding.u64 (Lynx.Rustler.encodeUnsigned value) = RustM.ok (.Ok value) := by
  have decoded := Lynx.Rustler.decodeUnsigned_encodeUnsigned value
  change Lynx.Rustler.decodeUnsigned .U64 64 (Lynx.Rustler.encodeUnsigned value) = .ok value at decoded
  simp [Lynx.Rustler.Decoding.u64, decoded]

theorem decoder_empty : OrderedReply.Insts.RustlerTypesDecoder.decode (.atom "empty") = RustM.ok (.Ok .Empty) := by
  simp [OrderedReply.Insts.RustlerTypesDecoder.decode, Lynx.Rustler.Decoding.atom,
    rustler_atoms_ordered_reply.atom_empty, TaggedDecode.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.atomEq, Lynx.Rustler.Decoding.dropScalarResult]

theorem decoder_equal (value : U64) : OrderedReply.Insts.RustlerTypesDecoder.decode
    (replyTerm (.Equal value)) = RustM.ok (.Ok (.Equal value)) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have two (h : 2 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 2 h = 2#usize :=
    (UScalar.eq_equiv _ _).mpr (by scalar_tac)
  have sub21 : (2#usize - 1#usize) = RustM.ok 1#usize := by
    have spec := Usize.sub_bv_spec (x := 2#usize) (y := 1#usize) (by scalar_tac)
    obtain ⟨result, returned, property⟩ := triple_iff_exists_ok.mp (WP.spec_to_mvcgen spec)
    have eq : result = 1#usize := (UScalar.eq_equiv _ _).mpr (by simpa using property.1)
    simpa [eq] using returned
  simp [two, sub21, OrderedReply.Insts.RustlerTypesDecoder.decode, replyTerm, Lynx.Rustler.Decoding.atom,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.deref, alloc.vec.Vec.len,
    core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    Slice.index_usize, TaggedDecode.Extraction.Option.andThen,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TermOptionAtom,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TermOptionAtom.call_once,
    Lynx.Rustler.Decoding.resultOk, Lynx.Rustler.Decoding.optionOkOr,
    rustler_atoms_ordered_reply.atom_empty, rustler_atoms_ordered_reply.atom_equal,
    rustler_atoms_ordered_reply.atom_ordered, TaggedDecode.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.atomEq, Lynx.Rustler.Decoding.dropScalarResult, Lynx.Rustler.Decoding.dropDecoderError,
    core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.map_err, decode_u64,
    alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    TaggedDecode.Extraction.ErrorConstants.literal_0, Lynx.Rustler.raiseAtomErrorOutcome,
    Lynx.Rustler.badArgOutcome]

theorem decoder_ordered (left right : U64) : OrderedReply.Insts.RustlerTypesDecoder.decode
    (replyTerm (.Ordered left right)) = RustM.ok (.Ok (.Ordered left right)) := by
  have bounds : (3 : Nat) ≤ Usize.max ∧ 3 ≤ Isize.max.toNat ∧ 3 ≤ 16777215 := by scalar_tac
  have three (h : 3 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 3 h = 3#usize :=
    (UScalar.eq_equiv _ _).mpr (by scalar_tac)
  have sub32 : (3#usize - 1#usize) = RustM.ok 2#usize := by
    have spec := Usize.sub_bv_spec (x := 3#usize) (y := 1#usize) (by scalar_tac)
    obtain ⟨result, returned, property⟩ := triple_iff_exists_ok.mp (WP.spec_to_mvcgen spec)
    have eq : result = 2#usize := (UScalar.eq_equiv _ _).mpr (by simpa using property.1)
    simpa [eq] using returned
  simp [three, sub32, OrderedReply.Insts.RustlerTypesDecoder.decode, replyTerm, Lynx.Rustler.Decoding.atom,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.deref, alloc.vec.Vec.len,
    core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    Slice.index_usize, TaggedDecode.Extraction.Option.andThen,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TermOptionAtom,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TermOptionAtom.call_once,
    Lynx.Rustler.Decoding.resultOk, Lynx.Rustler.Decoding.optionOkOr,
    rustler_atoms_ordered_reply.atom_empty, rustler_atoms_ordered_reply.atom_equal,
    rustler_atoms_ordered_reply.atom_ordered, TaggedDecode.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.atomEq, Lynx.Rustler.Decoding.dropScalarResult, Lynx.Rustler.Decoding.dropDecoderError,
    core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.map_err, decode_u64,
    alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    TaggedDecode.Extraction.ErrorConstants.literal_0, Lynx.Rustler.raiseAtomErrorOutcome,
    Lynx.Rustler.badArgOutcome]

theorem decoder_success (value : OrderedReply) :
    OrderedReply.Insts.RustlerTypesDecoder.decode (replyTerm value) = RustM.ok (.Ok value) := by
  cases value with
  | Empty => exact decoder_empty
  | Equal value => exact decoder_equal value
  | Ordered left right => exact decoder_ordered left right

theorem core_spec (left right : U64) :
    experiment_core.order_pair left right = RustM.ok (if left ≤ right then (left, right) else (right, left)) := by
  unfold experiment_core.order_pair
  split <;> rfl

theorem caller_spec (left right : U64) :
    experiment_analysis.order_pair left right = RustM.ok (if left ≤ right then (left, right) else (right, left)) := core_spec left right

@[expose] def normalise : OrderedReply → OrderedReply
  | .Ordered left right => if left ≤ right then .Ordered left right else .Ordered right left
  | value => value

theorem facade_spec (value : OrderedReply) :
    __FACADE__ value = RustM.ok (normalise value) := by
  cases value <;> simp [__FACADE__, normalise, caller_spec]
  split <;> rfl

theorem encoder_spec (value : OrderedReply) (env : Lynx.Rustler.Env) :
    OrderedReply.Insts.RustlerTypesEncoder.encode value env = RustM.ok (replyTerm value) := by
  cases value <;> simp [OrderedReply.Insts.RustlerTypesEncoder.encode, replyTerm,
    rustler_atoms_ordered_reply.atom_empty, rustler_atoms_ordered_reply.atom_equal,
    rustler_atoms_ordered_reply.atom_ordered, TaggedDecode.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.Encoding.atom, Lynx.Rustler.Encoding.pair, Lynx.Rustler.Encoding.triple,
    Lynx.Rustler.Encoding.shared, Lynx.Rustler.Encoding.u64,
    Lynx.Rustler.encodeUnsigned]

theorem invalid_constant : TaggedDecode.Extraction.ErrorConstants.literal_0 =
    Lynx.Rustler.raiseAtomErrorOutcome "invalid_variant" := by
  unfold TaggedDecode.Extraction.ErrorConstants.literal_0
  congr 1

theorem unknown_atom (tag : String) (unknown : tag ≠ "empty") :
    OrderedReply.Insts.RustlerTypesDecoder.decode (.atom tag) =
      RustM.ok (.Err (Lynx.Rustler.raiseAtomErrorOutcome "invalid_variant")) := by
  simp [OrderedReply.Insts.RustlerTypesDecoder.decode, Lynx.Rustler.Decoding.atom,
    rustler_atoms_ordered_reply.atom_empty, TaggedDecode.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.atomEq, unknown, Lynx.Rustler.Decoding.dropScalarResult, invalid_constant]

theorem empty_tuple : OrderedReply.Insts.RustlerTypesDecoder.decode (.tuple #[]) =
    RustM.ok (.Err (Lynx.Rustler.raiseAtomErrorOutcome "invalid_variant")) := by
  simp [OrderedReply.Insts.RustlerTypesDecoder.decode, Lynx.Rustler.Decoding.atom,
    Lynx.Rustler.Decoding.getTuple, alloc.vec.Vec.deref, core.slice.Slice.get,
    core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    TaggedDecode.Extraction.Option.andThen, Lynx.Rustler.Decoding.optionOkOr,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, Lynx.Rustler.Decoding.dropScalarResult,
    Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome, invalid_constant]

@[expose] def badField : Lynx.Rustler.DecoderError := Lynx.Rustler.raiseTermErrorOutcome
  (Dyn.mk _ alloc.string.String.Insts.RustlerTypesEncoder "Could not decode field on position 1")

theorem field_error_callback :
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once
      () Lynx.Rustler.badArgOutcome = RustM.ok badField := by
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "Could not decode field on position 1").val).toList = [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 111, 110, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 49] := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 111, 110, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 49]⟩ = some "Could not decode field on position 1" := by decide +kernel
  have bounded : "Could not decode field on position 1".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have size : "Could not decode field on position 1".utf8ByteSize = 36 := by decide +kernel
  have machine : "Could not decode field on position 1".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp [Decoder__rustler_decode_lifetimeOrderedReply.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
    badField, Lynx.RustFormatting.core.fmt.Arguments.from_str, Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.Formatting.writeBytes, fieldBytes, decoded, bounded, machine,
    Lynx.RustFormatting.Formatting.append, experiment_nif.core.hint.must_use,
    Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome]


theorem field_error (input : Lynx.Term)
    (rejected : Lynx.Rustler.Decoding.u64 input = RustM.ok (.Err Lynx.Rustler.badArgOutcome)) : OrderedReply.Insts.RustlerTypesDecoder.decode
    (.tuple #[.atom "equal", input]) = RustM.ok (.Err badField) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have two (h : 2 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 2 h = 2#usize :=
    (UScalar.eq_equiv _ _).mpr (by scalar_tac)
  have sub21 : (2#usize - 1#usize) = RustM.ok 1#usize := by
    have spec := Usize.sub_bv_spec (x := 2#usize) (y := 1#usize) (by scalar_tac)
    obtain ⟨result, returned, property⟩ := triple_iff_exists_ok.mp (WP.spec_to_mvcgen spec)
    have eq : result = 1#usize := (UScalar.eq_equiv _ _).mpr (by simpa using property.1)
    simpa [eq] using returned
  have callback := field_error_callback
  simp only [Lynx.Rustler.badArgOutcome] at callback
  simp [two, sub21, OrderedReply.Insts.RustlerTypesDecoder.decode, replyTerm, Lynx.Rustler.Decoding.atom,
    Lynx.Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.deref, alloc.vec.Vec.len,
    core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    Slice.index_usize, TaggedDecode.Extraction.Option.andThen,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TermOptionAtom,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure.Insts.CoreOpsFunctionFnOnceTupleShared1TermOptionAtom.call_once,
    Lynx.Rustler.Decoding.resultOk, Lynx.Rustler.Decoding.optionOkOr,
    rustler_atoms_ordered_reply.atom_empty, rustler_atoms_ordered_reply.atom_equal,
    rustler_atoms_ordered_reply.atom_ordered, TaggedDecode.Extraction.RustlerAtomCache.cache_0,
    Lynx.Rustler.atomEq, Lynx.Rustler.Decoding.dropScalarResult, Lynx.Rustler.Decoding.dropDecoderError,
    core.result.Result.Insts.CoreOpsTry.branch, core.result.Result.map_err, rejected,
    Decoder__rustler_decode_lifetimeOrderedReply.decode.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError, callback,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame,
    alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    TaggedDecode.Extraction.ErrorConstants.literal_0, Lynx.Rustler.raiseAtomErrorOutcome,
    Lynx.Rustler.badArgOutcome]


end TaggedDecode.Properties
