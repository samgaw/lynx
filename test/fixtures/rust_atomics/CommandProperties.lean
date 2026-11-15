module
public import Commands.Extraction.Funs
public import Commands.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Commands.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem read_decoded : commands.Command.Insts.RustlerTypesDecoder.decode (.atom "read") =
    NativeM.ok (.Ok .Read) := by rfl

theorem replacement_decoded (left right : U64) :
    commands.Replacement.Insts.RustlerTypesDecoder.decode
      (.tuple #[.integer left.val, .integer right.val]) =
      NativeM.ok (.Ok {expected := left, replacement := right}) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have decode (value : U64) : Rustler.NativeDecoding.u64 (.integer value.val) = NativeM.ok (.Ok value) := by
    have decoded := Rustler.decodeUnsigned_encodeUnsigned value
    change Rustler.decodeUnsigned .U64 64 (.integer value.val) = .ok value at decoded
    simp [Rustler.NativeDecoding.u64, Rustler.Decoding.u64, decoded, NativeM.lift, NativeM.fromRust, NativeM.ok]
  simp [commands.Replacement.Insts.RustlerTypesDecoder.decode,
    commands.Decoder__rustler_decode_lifetimeReplacement.decode.try_decode_index,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple, bounds,
    alloc.vec.Vec.len, alloc.vec.Vec.deref, Slice.index_usize,
    U64.Insts.RustlerTypesDecoder, decode,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]


theorem compare_decoded (input : Term) (request : commands.Replacement)
    (decoded : commands.Replacement.Insts.RustlerTypesDecoder.decode input = NativeM.ok (.Ok request)) :
    commands.Command.Insts.RustlerTypesDecoder.decode (.tuple #[.atom "compare", input]) =
      NativeM.ok (.Ok (.Compare request)) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have two (h : 2 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 2 h = 2#usize :=
    (UScalar.eq_equiv _ _).mpr (by scalar_tac)
  have sub21 : (2#usize - 1#usize) = RustM.ok 1#usize := by
    have spec := Usize.sub_bv_spec (x := 2#usize) (y := 1#usize) (by scalar_tac)
    obtain ⟨result, returned, property⟩ := triple_iff_exists_ok.mp (WP.spec_to_mvcgen spec)
    have eq : result = 1#usize := (UScalar.eq_equiv _ _).mpr (by simpa using property.1)
    simpa [eq] using returned
  simp [two, sub21, commands.Command.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom, Rustler.NativeDecoding.getTuple,
    Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.deref, alloc.vec.Vec.len,
    core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    Slice.index_usize, NativeCallbacks.andThen, NativeCallbacks.mapErr,
    commands.Decoder__rustler_decode_lifetimeCommand.decode.closure.Insts.Lynx_nativeFnOnceTupleShared1TermOptionAtom,
    commands.Decoder__rustler_decode_lifetimeCommand.decode.closure.Insts.Lynx_nativeFnOnceTupleShared1TermOptionAtom.call_once,
    Rustler.Decoding.resultOk, Rustler.Decoding.optionOkOr,
    Commands.Extraction.ErrorConstants.literal_0, Rustler.raiseAtomErrorOutcome, Rustler.badArgOutcome,
    commands.rustler_atoms_command.atom_read, commands.rustler_atoms_command.atom_compare,
    Commands.Extraction.RustlerAtomCache.cache_0, Rustler.atomEq,
    Rustler.Decoding.dropScalarResult, Rustler.Decoding.dropDecoderError,
    core.result.Result.Insts.CoreOpsTry.branch, decoded,
    alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem unknown_atom : commands.Command.Insts.RustlerTypesDecoder.decode (.atom "unknown") =
    NativeM.ok (.Err (Rustler.raiseAtomErrorOutcome "invalid_variant")) := by rfl

theorem replacement_shape_rejected :
    commands.Replacement.Insts.RustlerTypesDecoder.decode (.integer 0) =
      NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp [commands.Replacement.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.getTuple, Rustler.Decoding.getTuple,
    Rustler.badArgOutcome, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from,
    NativeM.lift, NativeM.fromRust, NativeM.ok]


@[expose] def badField : Lynx.Rustler.DecoderError := Lynx.Rustler.raiseTermErrorOutcome
  (Dyn.mk _ alloc.string.String.Insts.RustlerTypesEncoder "Could not decode field on position 1")

theorem field_error_callback :
    commands.Decoder__rustler_decode_lifetimeCommand.decode.closure_1.Insts.Lynx_nativeFnOnceTupleErrorError.call_once
      () Lynx.Rustler.badArgOutcome = NativeM.ok badField := by
  have fieldBytes : (Lynx.RustFormatting.Formatting.bytes (toStr "Could not decode field on position 1").val).toList = [67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 111, 110, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 49] := by decide +kernel
  have decoded : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 111, 110, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 49]⟩ = some "Could not decode field on position 1" := by decide +kernel
  have bounded : "Could not decode field on position 1".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have size : "Could not decode field on position 1".utf8ByteSize = 36 := by decide +kernel
  have machine : "Could not decode field on position 1".utf8ByteSize ≤ Isize.max.toNat := by rw [size]; scalar_tac
  simp [commands.Decoder__rustler_decode_lifetimeCommand.decode.closure_1.Insts.Lynx_nativeFnOnceTupleErrorError.call_once,
    badField, Lynx.RustFormatting.core.fmt.Arguments.from_str, Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.Formatting.writeBytes, fieldBytes, decoded, bounded, machine,
    Lynx.RustFormatting.Formatting.append, atomic_nif.core.hint.must_use,
    Lynx.Rustler.Decoding.dropDecoderError, Lynx.Rustler.badArgOutcome, NativeM.lift, NativeM.fromRust, NativeM.ok]



theorem compare_rejected (input : Term)
    (decoded : commands.Replacement.Insts.RustlerTypesDecoder.decode input = NativeM.ok (.Err Rustler.badArgOutcome)) :
    commands.Command.Insts.RustlerTypesDecoder.decode (.tuple #[.atom "compare", input]) =
      NativeM.ok (.Err badField) := by
  have bounds : (2 : Nat) ≤ Usize.max ∧ 2 ≤ Isize.max.toNat ∧ 2 ≤ 16777215 := by scalar_tac
  have two (h : 2 < 2 ^ UScalarTy.Usize.numBits) : Usize.ofNatCore 2 h = 2#usize :=
    (UScalar.eq_equiv _ _).mpr (by scalar_tac)
  have sub21 : (2#usize - 1#usize) = RustM.ok 1#usize := by
    have spec := Usize.sub_bv_spec (x := 2#usize) (y := 1#usize) (by scalar_tac)
    obtain ⟨result, returned, property⟩ := triple_iff_exists_ok.mp (WP.spec_to_mvcgen spec)
    have eq : result = 1#usize := (UScalar.eq_equiv _ _).mpr (by simpa using property.1)
    simpa [eq] using returned
  have callback := field_error_callback
  simp only [Rustler.badArgOutcome] at callback
  simp [two, sub21, commands.Command.Insts.RustlerTypesDecoder.decode,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom, Rustler.NativeDecoding.getTuple,
    Rustler.Decoding.getTuple, bounds, alloc.vec.Vec.deref, alloc.vec.Vec.len,
    core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice, core.slice.index.Usize.get,
    Slice.index_usize, NativeCallbacks.andThen, NativeCallbacks.mapErr,
    commands.Decoder__rustler_decode_lifetimeCommand.decode.closure.Insts.Lynx_nativeFnOnceTupleShared1TermOptionAtom,
    commands.Decoder__rustler_decode_lifetimeCommand.decode.closure.Insts.Lynx_nativeFnOnceTupleShared1TermOptionAtom.call_once,
    Rustler.Decoding.resultOk, Rustler.Decoding.optionOkOr,
    Commands.Extraction.ErrorConstants.literal_0, Rustler.raiseAtomErrorOutcome, Rustler.badArgOutcome,
    commands.rustler_atoms_command.atom_read, commands.rustler_atoms_command.atom_compare,
    Commands.Extraction.RustlerAtomCache.cache_0, Rustler.atomEq,
    Rustler.Decoding.dropScalarResult, Rustler.Decoding.dropDecoderError,
    core.result.Result.Insts.CoreOpsTry.branch, decoded,
    alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_usize,
    commands.Decoder__rustler_decode_lifetimeCommand.decode.closure_1.Insts.Lynx_nativeFnOnceTupleErrorError, callback,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, core.convert.FromSame.from, NativeM.lift, NativeM.fromRust, NativeM.ok]


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


theorem updated (previous replacement : U64)
    (schedule : List ScheduleChoice) :
    (commands.execute ⟨2,3⟩ (.Compare {expected := previous, replacement})).run
      (retained previous) schedule =
      (.ok (true, previous), afterCall replacement) := by
  simp [commands.execute, composed, contract, current_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.load,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide


theorem read_preserved (previous : U64)
    (schedule : List ScheduleChoice) :
    (commands.execute ⟨2,3⟩ .Read).run
      (retained previous) schedule =
      (.ok (false, previous), afterCall (previous)) := by
  simp [commands.execute, composed, contract, current_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.load,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide


theorem mismatched (previous expected replacement : U64)
    (different : previous ≠ expected)
    (schedule : List ScheduleChoice) :
    (commands.execute ⟨2,3⟩ (.Compare {expected, replacement})).run
      (retained previous) schedule =
      (.ok (false, previous), afterCall previous) := by
  simp [commands.execute, composed, contract, current_contract, retained, afterCall, different,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.load,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide




theorem nested_rejected_encoded (input : Term)
    (rejected : commands.Replacement.Insts.RustlerTypesDecoder.decode input =
      NativeM.ok (.Err Rustler.badArgOutcome)) :
    commands.Command.Insts.RustlerTypesDecoder.decode (.tuple #[.atom "compare", input]) =
      NativeM.ok (.Err (.encoded true (fun _ => RustM.ok
        (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 111, 110, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 49]⟩ 0)))) := by
  have size : "Could not decode field on position 1".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have encoded (env : Rustler.Env) : Rustler.Encoding.string "Could not decode field on position 1" env =
      RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 111, 110, 32, 112, 111, 115, 105, 116, 105, 111, 110, 32, 49]⟩ 0) := by
    simp [Rustler.Encoding.string, size]
    decide +kernel
  simpa only [badField, Rustler.raiseTermErrorOutcome,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, encoded] using compare_rejected input rejected

/-- The actual Rustler facade invokes the internal command implementation. -/
theorem facade_spec (resource : NativeResourceArc Counter) (input : commands.Command) :
    __COMMAND__ resource input = commands.execute resource input := by rfl

/-- The ordinary Rustler allocation and read facade bodies are also extracted. -/
theorem facade_new (value : U64) : __NEW__ value = atomic_nif.counter_new value := by rfl

theorem facade_read (resource : NativeResourceArc Counter) :
    __READ__ resource = atomic_nif.counter_read resource := by rfl

end Commands.Properties
