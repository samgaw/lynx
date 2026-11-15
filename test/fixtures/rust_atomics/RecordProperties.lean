module
public import Records.Extraction.Funs
public import Records.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Records.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private theorem decoded_u64 (value : U64) :
    Rustler.NativeDecoding.u64 (Rustler.encodeUnsigned value) = NativeM.ok (.Ok value) := by
  have decoded := Rustler.decodeUnsigned_encodeUnsigned value
  change Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned value) = .ok value at decoded
  simp [Rustler.NativeDecoding.u64, Rustler.Decoding.u64, decoded,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_field_success {T : Type} (decoder : Rustler.NativeDecoder T)
    (entries : List (Term × Term)) (field : String) (input : Term) (value : T)
    (found : Term.mapLookup entries (.atom field) = some input)
    (decoded : decoder.decode input = NativeM.ok (.Ok value)) :
    records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field
      decoder (.map entries) field = NativeM.ok (.Ok value) := by
  simp [records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field,
    Rustler.Decoding.mapGet, Shared0T.Insts.RustlerTypesEncoder,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    Rustler.Encoding.shared, Rustler.Encoding.atom, found, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_success (entries : List (Term × Term)) (expected replacement : U64)
    (first : Term.mapLookup entries (.atom "expected") = some (Rustler.encodeUnsigned expected))
    (second : Term.mapLookup entries (.atom "replacement") = some (Rustler.encodeUnsigned replacement)) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Ok {expected, replacement}) := by
  simp [records.MapRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_map_request.atom_expected,
    records.rustler_atoms_map_request.atom_replacement,
    Records.Extraction.RustlerAtomCache.cache_0,
    map_field_success U64.Insts.RustlerTypesDecoder _ _ _ _ first (decoded_u64 expected),
    map_field_success U64.Insts.RustlerTypesDecoder _ _ _ _ second (decoded_u64 replacement),
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem struct_field_success {T : Type} (decoder : Rustler.NativeDecoder T)
    (entries : List (Term × Term)) (field : String) (input : Term) (value : T)
    (found : Term.mapLookup entries (.atom field) = some input)
    (decoded : decoder.decode input = NativeM.ok (.Ok value)) :
    records.Decoder__rustler_decode_lifetimeStructRequest.decode.try_decode_field
      decoder (.map entries) field = NativeM.ok (.Ok value) := by
  simp [records.Decoder__rustler_decode_lifetimeStructRequest.decode.try_decode_field,
    Rustler.Decoding.mapGet, Shared0T.Insts.RustlerTypesEncoder,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    Rustler.Encoding.shared, Rustler.Encoding.atom, found, decoded,
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem struct_success (entries : List (Term × Term)) (expected replacement : U64)
    (tag : Term.mapLookup entries (.atom "__struct__") = some (.atom "Elixir.LynxRecordFixture.Request"))
    (first : Term.mapLookup entries (.atom "expected") = some (Rustler.encodeUnsigned expected))
    (second : Term.mapLookup entries (.atom "replacement") = some (Rustler.encodeUnsigned replacement)) :
    records.StructRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Ok {expected, replacement}) := by
  simp [records.StructRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_struct_request.atom_expected,
    records.rustler_atoms_struct_request.atom_replacement,
    records.rustler_atoms_struct_request.atom_struct,
    records.rustler_atoms_struct_request.atom_module,
    Rustler.Decoding.mapGet, Rustler.Encoding.atom, tag,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    rustler.term.Term.decode, rustler.types.atom.Atom.Insts.RustlerTypesDecoder,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom,
    Rustler.atomDefaultNe_eq rustler.types.atom.Atom.Insts.CoreCmpPartialEqAtom rfl,
    Records.Extraction.RustlerAtomCache.cache_1,
    struct_field_success U64.Insts.RustlerTypesDecoder _ _ _ _ first (decoded_u64 expected),
    struct_field_success U64.Insts.RustlerTypesDecoder _ _ _ _ second (decoded_u64 replacement),
    core.result.Result.Insts.CoreOpsTry.branch, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_core.replace counter expected replacement =
      NativeAtomic.compareExchange counter expected replacement .SeqCst .SeqCst := by rfl

theorem composed (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_analysis.try_set counter expected replacement = (do
      let result ← atomic_core.replace counter expected replacement
      match result with
      | .Ok previous => NativeM.ok (true, previous)
      | .Err observed => NativeM.ok (false, observed)) := by rfl

theorem resource_contract (owner : NativeResourceArc Counter) (request : records.MapRequest) :
    records.update_map owner request = (do
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
    (records.update_map ⟨2,3⟩ {expected := previous, replacement}).run (retained previous) schedule =
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
    (records.update_map ⟨2,3⟩ {expected, replacement}).run (retained previous) schedule =
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


theorem updates_agree (owner : NativeResourceArc Counter) (expected replacement : U64) :
    records.update_struct owner {expected, replacement} =
      records.update_map owner {expected, replacement} := by rfl


theorem map_field_missing {T : Type} (decoder : Rustler.NativeDecoder T)
    (entries : List (Term × Term)) (field : String)
    (missing : Term.mapLookup entries (.atom field) = none) :
    records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field
      decoder (.map entries) field = NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp [records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field,
    Rustler.Decoding.mapGet, Shared0T.Insts.RustlerTypesEncoder,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    Rustler.Encoding.shared, Rustler.Encoding.atom, missing,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_missing_first (entries : List (Term × Term))
    (missing : Term.mapLookup entries (.atom "expected") = none) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp [records.MapRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_map_request.atom_expected,
    Records.Extraction.RustlerAtomCache.cache_0,
    map_field_missing U64.Insts.RustlerTypesDecoder _ _ missing,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_missing_second (entries : List (Term × Term)) (expected : U64)
    (first : Term.mapLookup entries (.atom "expected") = some (Rustler.encodeUnsigned expected))
    (missing : Term.mapLookup entries (.atom "replacement") = none) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp [records.MapRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_map_request.atom_expected,
    records.rustler_atoms_map_request.atom_replacement,
    Records.Extraction.RustlerAtomCache.cache_0,
    map_field_success U64.Insts.RustlerTypesDecoder _ _ _ _ first (decoded_u64 expected),
    map_field_missing U64.Insts.RustlerTypesDecoder _ _ missing,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_nonmap (value : Int) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.integer value) =
      NativeM.ok (.Err Rustler.badArgOutcome) := by
  simp [records.MapRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_map_request.atom_expected,
    Records.Extraction.RustlerAtomCache.cache_0,
    records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field,
    Rustler.Decoding.mapGet, Shared0T.Insts.RustlerTypesEncoder,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    Rustler.Encoding.shared, Rustler.Encoding.atom,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem struct_missing_tag (entries : List (Term × Term))
    (tag : Term.mapLookup entries (.atom "__struct__") = none) :
    records.StructRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (Rustler.badArgOutcome)) := by
  simp [records.StructRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_struct_request.atom_struct,
    records.rustler_atoms_struct_request.atom_module,
    Records.Extraction.RustlerAtomCache.cache_1, tag,
    Rustler.Decoding.mapGet, Rustler.Encoding.atom,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    rustler.term.Term.decode, rustler.types.atom.Atom.Insts.RustlerTypesDecoder,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom,
    Rustler.atomDefaultNe_eq rustler.types.atom.Atom.Insts.CoreCmpPartialEqAtom rfl,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem struct_nonatom_tag (entries : List (Term × Term))
    (value : Int) (tag : Term.mapLookup entries (.atom "__struct__") = some (.integer value)) :
    records.StructRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (Rustler.badArgOutcome)) := by
  simp [records.StructRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_struct_request.atom_struct,
    records.rustler_atoms_struct_request.atom_module,
    Records.Extraction.RustlerAtomCache.cache_1, tag,
    Rustler.Decoding.mapGet, Rustler.Encoding.atom,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    rustler.term.Term.decode, rustler.types.atom.Atom.Insts.RustlerTypesDecoder,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom,
    Rustler.atomDefaultNe_eq rustler.types.atom.Atom.Insts.CoreCmpPartialEqAtom rfl,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem struct_wrong_tag (entries : List (Term × Term))
    (value : String) (wrong : value ≠ "Elixir.LynxRecordFixture.Request")
    (tag : Term.mapLookup entries (.atom "__struct__") = some (.atom value)) :
    records.StructRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (Rustler.raiseAtomErrorOutcome "invalid_struct")) := by
  simp [records.StructRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_struct_request.atom_struct,
    records.rustler_atoms_struct_request.atom_module,
    Records.Extraction.RustlerAtomCache.cache_1, tag,
    Rustler.Decoding.mapGet, Rustler.Encoding.atom,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    rustler.term.Term.decode, rustler.types.atom.Atom.Insts.RustlerTypesDecoder,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom,
    Rustler.atomDefaultNe_eq rustler.types.atom.Atom.Insts.CoreCmpPartialEqAtom rfl,
    wrong, Records.Extraction.ErrorConstants.literal_0,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_field_error (entries : List (Lynx.Term × Lynx.Term)) (input : Lynx.Term)
    (found : Lynx.Term.mapLookup entries (.atom "expected") = some input)
    (rejected : Lynx.Rustler.NativeDecoding.u64 input = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field
      atomic_nif.U64.Insts.RustlerTypesDecoder (.map entries) "expected" =
        NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
          ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
            "Could not decode field :expected on %{}"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [24#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 58#u8, 192#u8, 7#u8, 32#u8, 111#u8, 110#u8, 32#u8, 37#u8, 123#u8, 125#u8, 0#u8]).toList = [24, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 192, 7, 32, 111, 110, 32, 37, 123, 125, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58]⟩ = some "Could not decode field :" := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 37, 123, 125]⟩ = some " on %{}" := by decide +kernel
  have bare : Lynx.RustFormatting.Formatting.bareAtom "expected" = true := by simp [Lynx.RustFormatting.Formatting.bareAtom] <;> decide +kernel
  simp [records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field,
    Lynx.Rustler.Decoding.mapGet, Lynx.Rustler.Encoding.shared, Lynx.Rustler.Encoding.atom,
    found, rejected, core.result.Result.Insts.CoreOpsTry.branch,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_debug,
    Lynx.RustFormatting.rustler.atom.Debug.fmt,
    Lynx.RustFormatting.Formatting.bareAtom,
    Lynx.RustFormatting.core.fmt.Arguments.new,
    Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes,
    Lynx.RustFormatting.Formatting.append,
    Array.make, atomic_nif.core.hint.must_use, program, decodedPrefix, decodedSuffix, bare, Lynx.Rustler.Decoding.dropDecoderError,
    NativeM.lift, NativeM.fromRust, NativeM.ok, Lynx.Rustler.badArgOutcome]
  have smallPrefix : "Could not decode field :".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallAtom : "expected".utf8ByteSize ≤ 255 := by decide +kernel
  have smallField : "Could not decode field :".utf8ByteSize + "expected".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallMessage : "Could not decode field :".utf8ByteSize + "expected".utf8ByteSize + " on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have finalSize : "Could not decode field :expected on %{}".utf8ByteSize = 39 := by decide +kernel
  have machine : "Could not decode field :expected on %{}".utf8ByteSize ≤ Isize.max.toNat := by rw [finalSize]; scalar_tac
  have smallJoined : "Could not decode field :expected".utf8ByteSize + " on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallFinal : "Could not decode field :expected on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field :" ++ "expected" ++ " on %{}" = "Could not decode field :expected on %{}" := by decide +kernel
  simp_all [String.utf8ByteSize_append, NativeM.lift, NativeM.fromRust, NativeM.ok]




theorem map_second_field_error (entries : List (Lynx.Term × Lynx.Term)) (input : Lynx.Term)
    (found : Lynx.Term.mapLookup entries (.atom "replacement") = some input)
    (rejected : Lynx.Rustler.NativeDecoding.u64 input = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field
      atomic_nif.U64.Insts.RustlerTypesDecoder (.map entries) "replacement" =
        NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
          ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
            "Could not decode field :replacement on %{}"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [24#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 58#u8, 192#u8, 7#u8, 32#u8, 111#u8, 110#u8, 32#u8, 37#u8, 123#u8, 125#u8, 0#u8]).toList = [24, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 192, 7, 32, 111, 110, 32, 37, 123, 125, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58]⟩ = some "Could not decode field :" := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 37, 123, 125]⟩ = some " on %{}" := by decide +kernel
  have bare : Lynx.RustFormatting.Formatting.bareAtom "replacement" = true := by simp [Lynx.RustFormatting.Formatting.bareAtom] <;> decide +kernel
  simp [records.Decoder__rustler_decode_lifetimeMapRequest.decode.try_decode_field,
    Lynx.Rustler.Decoding.mapGet, Lynx.Rustler.Encoding.shared, Lynx.Rustler.Encoding.atom,
    found, rejected, core.result.Result.Insts.CoreOpsTry.branch,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_debug,
    Lynx.RustFormatting.rustler.atom.Debug.fmt,
    Lynx.RustFormatting.Formatting.bareAtom,
    Lynx.RustFormatting.core.fmt.Arguments.new,
    Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes,
    Lynx.RustFormatting.Formatting.append,
    Array.make, atomic_nif.core.hint.must_use, program, decodedPrefix, decodedSuffix, bare, Lynx.Rustler.Decoding.dropDecoderError,
    NativeM.lift, NativeM.fromRust, NativeM.ok, Lynx.Rustler.badArgOutcome]
  have smallPrefix : "Could not decode field :".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallAtom : "replacement".utf8ByteSize ≤ 255 := by decide +kernel
  have smallField : "Could not decode field :".utf8ByteSize + "replacement".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallMessage : "Could not decode field :".utf8ByteSize + "replacement".utf8ByteSize + " on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have finalSize : "Could not decode field :replacement on %{}".utf8ByteSize = 42 := by decide +kernel
  have machine : "Could not decode field :replacement on %{}".utf8ByteSize ≤ Isize.max.toNat := by rw [finalSize]; scalar_tac
  have smallJoined : "Could not decode field :replacement".utf8ByteSize + " on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallFinal : "Could not decode field :replacement on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field :" ++ "replacement" ++ " on %{}" = "Could not decode field :replacement on %{}" := by decide +kernel
  simp_all [String.utf8ByteSize_append, NativeM.lift, NativeM.fromRust, NativeM.ok]




theorem struct_field_error (entries : List (Lynx.Term × Lynx.Term)) (input : Lynx.Term)
    (found : Lynx.Term.mapLookup entries (.atom "expected") = some input)
    (rejected : Lynx.Rustler.NativeDecoding.u64 input = NativeM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    records.Decoder__rustler_decode_lifetimeStructRequest.decode.try_decode_field
      atomic_nif.U64.Insts.RustlerTypesDecoder (.map entries) "expected" =
        NativeM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
          ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
            "Could not decode field :expected on %StructRequest{}"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [24#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 58#u8, 192#u8, 20#u8, 32#u8, 111#u8, 110#u8, 32#u8, 37#u8, 83#u8, 116#u8, 114#u8, 117#u8, 99#u8, 116#u8, 82#u8, 101#u8, 113#u8, 117#u8, 101#u8, 115#u8, 116#u8, 123#u8, 125#u8, 0#u8]).toList = [24, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 192, 20, 32, 111, 110, 32, 37, 83, 116, 114, 117, 99, 116, 82, 101, 113, 117, 101, 115, 116, 123, 125, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58]⟩ = some "Could not decode field :" := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 37, 83, 116, 114, 117, 99, 116, 82, 101, 113, 117, 101, 115, 116, 123, 125]⟩ = some " on %StructRequest{}" := by decide +kernel
  have bare : Lynx.RustFormatting.Formatting.bareAtom "expected" = true := by simp [Lynx.RustFormatting.Formatting.bareAtom] <;> decide +kernel
  simp [records.Decoder__rustler_decode_lifetimeStructRequest.decode.try_decode_field,
    Lynx.Rustler.Decoding.mapGet, Lynx.Rustler.Encoding.shared, Lynx.Rustler.Encoding.atom,
    found, rejected, core.result.Result.Insts.CoreOpsTry.branch,
    Lynx.RustFormatting.core.fmt.rt.Argument.new_debug,
    Lynx.RustFormatting.rustler.atom.Debug.fmt,
    Lynx.RustFormatting.Formatting.bareAtom,
    Lynx.RustFormatting.core.fmt.Arguments.new,
    Lynx.RustFormatting.Formatting.validTemplate,
    Lynx.RustFormatting.alloc.fmt.format,
    Lynx.RustFormatting.Formatting.run, Lynx.RustFormatting.Formatting.writeBytes,
    Lynx.RustFormatting.Formatting.append,
    Array.make, atomic_nif.core.hint.must_use, program, decodedPrefix, decodedSuffix, bare, Lynx.Rustler.Decoding.dropDecoderError,
    NativeM.lift, NativeM.fromRust, NativeM.ok, Lynx.Rustler.badArgOutcome]
  have smallPrefix : "Could not decode field :".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallAtom : "expected".utf8ByteSize ≤ 255 := by decide +kernel
  have smallField : "Could not decode field :".utf8ByteSize + "expected".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallMessage : "Could not decode field :".utf8ByteSize + "expected".utf8ByteSize + " on %StructRequest{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have finalSize : "Could not decode field :expected on %StructRequest{}".utf8ByteSize = 52 := by decide +kernel
  have machine : "Could not decode field :expected on %StructRequest{}".utf8ByteSize ≤ Isize.max.toNat := by rw [finalSize]; scalar_tac
  have smallJoined : "Could not decode field :expected".utf8ByteSize + " on %StructRequest{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallFinal : "Could not decode field :expected on %StructRequest{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field :" ++ "expected" ++ " on %StructRequest{}" = "Could not decode field :expected on %StructRequest{}" := by decide +kernel
  simp_all [String.utf8ByteSize_append, NativeM.lift, NativeM.fromRust, NativeM.ok]


theorem map_expected_error (entries : List (Term × Term)) (bad : Term)
    (found : Term.mapLookup entries (.atom "expected") = some bad)
    (rejected : Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field :expected on %{}"⟩)) := by
  simp [records.MapRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_map_request.atom_expected,
    records.rustler_atoms_map_request.atom_replacement,
    Records.Extraction.RustlerAtomCache.cache_0,
    map_field_error _ _ found rejected,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_replacement_error (entries : List (Term × Term)) (bad : Term)
    (expected : U64) (first : Term.mapLookup entries (.atom "expected") = some (Rustler.encodeUnsigned expected))
    (found : Term.mapLookup entries (.atom "replacement") = some bad)
    (rejected : Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field :replacement on %{}"⟩)) := by
  simp [records.MapRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_map_request.atom_expected,
    records.rustler_atoms_map_request.atom_replacement,
    Records.Extraction.RustlerAtomCache.cache_0,
    map_second_field_error _ _ found rejected,
    map_field_success U64.Insts.RustlerTypesDecoder _ _ _ _ first (decoded_u64 expected),
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem struct_expected_error (entries : List (Term × Term)) (bad : Term)
    (tag : Term.mapLookup entries (.atom "__struct__") = some (.atom "Elixir.LynxRecordFixture.Request"))
    (found : Term.mapLookup entries (.atom "expected") = some bad)
    (rejected : Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    records.StructRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (Rustler.raiseTermErrorOutcome
        ⟨String, atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, "Could not decode field :expected on %StructRequest{}"⟩)) := by
  simp [records.StructRequest.Insts.RustlerTypesDecoder.decode,
    records.rustler_atoms_struct_request.atom_expected,
    records.rustler_atoms_struct_request.atom_replacement,
    Records.Extraction.RustlerAtomCache.cache_1,
    struct_field_error _ _ found rejected,
    records.rustler_atoms_struct_request.atom_struct,
    records.rustler_atoms_struct_request.atom_module,
    Rustler.Decoding.mapGet, Rustler.Encoding.atom, tag,
    rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    rustler.term.Term.decode, rustler.types.atom.Atom.Insts.RustlerTypesDecoder,
    Rustler.NativeDecoding.atom, Rustler.Decoding.atom,
    Rustler.atomDefaultNe_eq rustler.types.atom.Atom.Insts.CoreCmpPartialEqAtom rfl,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem map_expected_encoded (entries : List (Term × Term)) (bad : Term)
    (found : Term.mapLookup entries (.atom "expected") = some bad)
    (rejected : Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (.encoded true (fun _ => RustM.ok
        (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 37, 123, 125]⟩ 0)))) := by
  have size : "Could not decode field :expected on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have encoded (env : Rustler.Env) : Rustler.Encoding.string "Could not decode field :expected on %{}" env =
      RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 37, 123, 125]⟩ 0) := by
    simp [Rustler.Encoding.string, size]
    decide +kernel
  simpa only [Rustler.raiseTermErrorOutcome,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, encoded] using
    map_expected_error entries bad found rejected

theorem map_replacement_encoded (entries : List (Term × Term)) (bad : Term)
    (expected : U64) (first : Term.mapLookup entries (.atom "expected") = some (Rustler.encodeUnsigned expected))
    (found : Term.mapLookup entries (.atom "replacement") = some bad)
    (rejected : Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    records.MapRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (.encoded true (fun _ => RustM.ok
        (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116, 32, 111, 110, 32, 37, 123, 125]⟩ 0)))) := by
  have size : "Could not decode field :replacement on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have encoded (env : Rustler.Env) : Rustler.Encoding.string "Could not decode field :replacement on %{}" env =
      RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116, 32, 111, 110, 32, 37, 123, 125]⟩ 0) := by
    simp [Rustler.Encoding.string, size]
    decide +kernel
  simpa only [Rustler.raiseTermErrorOutcome,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, encoded] using
    map_replacement_error entries bad expected first found rejected

theorem struct_expected_encoded (entries : List (Term × Term)) (bad : Term)
    (tag : Term.mapLookup entries (.atom "__struct__") = some (.atom "Elixir.LynxRecordFixture.Request"))
    (found : Term.mapLookup entries (.atom "expected") = some bad)
    (rejected : Rustler.NativeDecoding.u64 bad = NativeM.ok (.Err Rustler.badArgOutcome)) :
    records.StructRequest.Insts.RustlerTypesDecoder.decode (.map entries) =
      NativeM.ok (.Err (.encoded true (fun _ => RustM.ok
        (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 37, 83, 116, 114, 117, 99, 116, 82, 101, 113, 117, 101, 115, 116, 123, 125]⟩ 0)))) := by
  have size : "Could not decode field :expected on %StructRequest{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have encoded (env : Rustler.Env) : Rustler.Encoding.string "Could not decode field :expected on %StructRequest{}" env =
      RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 37, 83, 116, 114, 117, 99, 116, 82, 101, 113, 117, 101, 115, 116, 123, 125]⟩ 0) := by
    simp [Rustler.Encoding.string, size]
    decide +kernel
  simpa only [Rustler.raiseTermErrorOutcome,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder, encoded] using
    struct_expected_error entries bad tag found rejected

end Records.Properties
