module
public import RustWorkspace.MapDecodeFacade.Funs
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std
namespace RustWorkspace.DerivedMapDecoder

theorem core_spec (left right : U64) :
    experiment_nif.experiment_core.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := by
  unfold experiment_nif.experiment_core.order_pair
  split <;> rfl

theorem caller_spec (left right : U64) :
    experiment_nif.experiment_analysis.order_pair left right =
      RustM.ok (if left ≤ right then (left, right) else (right, left)) := core_spec left right

theorem field_success {T : Type} (decoder : Lynx.Rustler.Decoder T)
    (entries : List (Lynx.Term × Lynx.Term)) (field : String) (input : Lynx.Term) (value : T)
    (found : Lynx.Term.mapLookup entries (.atom field) = some input)
    (decoded : decoder.decode input = RustM.ok (.Ok value)) :
    experiment_nif.Decoder__rustler_decode_lifetimeOrderedMap.decode.try_decode_field
      decoder (.map entries) field = RustM.ok (.Ok value) := by
  simp [experiment_nif.Decoder__rustler_decode_lifetimeOrderedMap.decode.try_decode_field,
    Lynx.Rustler.Decoding.mapGet, experiment_nif.Shared0T.Insts.RustlerTypesEncoder,
    experiment_nif.rustler.types.atom.Atom.Insts.RustlerTypesEncoder,
    Lynx.Rustler.Encoding.shared, Lynx.Rustler.Encoding.atom,
    found, decoded, core.result.Result.Insts.CoreOpsTry.branch]

theorem decoder_success (entries : List (Lynx.Term × Lynx.Term)) (low high : U64)
    (foundLow : Lynx.Term.mapLookup entries (.atom "low") = some (Lynx.Rustler.encodeUnsigned low))
    (foundHigh : Lynx.Term.mapLookup entries (.atom "high") = some (Lynx.Rustler.encodeUnsigned high)) :
    experiment_nif.OrderedMap.Insts.RustlerTypesDecoder.decode (.map entries) =
      RustM.ok (.Ok {low, high}) := by
  have decoded (v : U64) : experiment_nif.U64.Insts.RustlerTypesDecoder.decode
      (Lynx.Rustler.encodeUnsigned v) = RustM.ok (.Ok v) := by
    have valid := Lynx.Rustler.decodeUnsigned_encodeUnsigned v
    change Lynx.Rustler.decodeUnsigned .U64 64 (Lynx.Rustler.encodeUnsigned v) = .ok v at valid
    simp [experiment_nif.U64.Insts.RustlerTypesDecoder, Lynx.Rustler.Decoding.u64, valid]
  simp [experiment_nif.OrderedMap.Insts.RustlerTypesDecoder.decode,
    experiment_nif.rustler_atoms_ordered_map.atom_low,
    experiment_nif.rustler_atoms_ordered_map.atom_high,
    RustWorkspace.MapDecodeFacade.RustlerAtomCache.cache_0,
    field_success _ _ _ _ _ foundLow (decoded low),
    field_success _ _ _ _ _ foundHigh (decoded high),
    core.result.Result.Insts.CoreOpsTry.branch]

theorem field_low_error (entries : List (Lynx.Term × Lynx.Term)) (input : Lynx.Term)
    (found : Lynx.Term.mapLookup entries (.atom "low") = some input)
    (rejected : Lynx.Rustler.Decoding.u64 input = RustM.ok (.Err Lynx.Rustler.badArgOutcome)) :
    experiment_nif.Decoder__rustler_decode_lifetimeOrderedMap.decode.try_decode_field
      experiment_nif.U64.Insts.RustlerTypesDecoder (.map entries) "low" =
        RustM.ok (.Err (Lynx.Rustler.raiseTermErrorOutcome
          ⟨String, experiment_nif.alloc.string.String.Insts.RustlerTypesEncoder,
            "Could not decode field :low on %{}"⟩)) := by
  have program : (Lynx.RustFormatting.Formatting.bytes [24#u8, 67#u8, 111#u8, 117#u8, 108#u8, 100#u8, 32#u8, 110#u8, 111#u8, 116#u8, 32#u8, 100#u8, 101#u8, 99#u8, 111#u8, 100#u8, 101#u8, 32#u8, 102#u8, 105#u8, 101#u8, 108#u8, 100#u8, 32#u8, 58#u8, 192#u8, 7#u8, 32#u8, 111#u8, 110#u8, 32#u8, 37#u8, 123#u8, 125#u8, 0#u8]).toList = [24, 67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58, 192, 7, 32, 111, 110, 32, 37, 123, 125, 0] := by decide +kernel
  have decodedPrefix : String.fromUTF8? ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 58]⟩ = some "Could not decode field :" := by decide +kernel
  have decodedSuffix : String.fromUTF8? ⟨#[32, 111, 110, 32, 37, 123, 125]⟩ = some " on %{}" := by decide +kernel
  have bare : Lynx.RustFormatting.Formatting.bareAtom "low" = true := by simp [Lynx.RustFormatting.Formatting.bareAtom] <;> decide +kernel
  simp [experiment_nif.Decoder__rustler_decode_lifetimeOrderedMap.decode.try_decode_field,
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
    Array.make, experiment_nif.core.hint.must_use, program, decodedPrefix, decodedSuffix, bare, Lynx.Rustler.Decoding.dropDecoderError,
    Lynx.Rustler.badArgOutcome]
  have smallPrefix : "Could not decode field :".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallAtom : "low".utf8ByteSize ≤ 255 := by decide +kernel
  have smallField : "Could not decode field :".utf8ByteSize + "low".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallMessage : "Could not decode field :".utf8ByteSize + "low".utf8ByteSize + " on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have finalSize : "Could not decode field :low on %{}".utf8ByteSize = 34 := by decide +kernel
  have machine : "Could not decode field :low on %{}".utf8ByteSize ≤ Isize.max.toNat := by rw [finalSize]; scalar_tac
  have smallJoined : "Could not decode field :low".utf8ByteSize + " on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have smallFinal : "Could not decode field :low on %{}".utf8ByteSize ≤ 4294967295 := by decide +kernel
  have joined : "Could not decode field :" ++ "low" ++ " on %{}" = "Could not decode field :low on %{}" := by decide +kernel
  simp_all [String.utf8ByteSize_append]


theorem facade_spec (value : experiment_nif.OrderedMap) :
    experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.ordered_map value =
      RustM.ok (if value.low ≤ value.high then value else {low := value.high, high := value.low}) := by
  cases value with
  | mk low high =>
    by_cases ordered : low ≤ high <;>
      simp [experiment_nif.__11.__INVENTORY.nif_func.wrapper.closure.ordered_map,
        caller_spec, ordered]

theorem encoder_spec (value : experiment_nif.OrderedMap) (env : Lynx.Rustler.Env) :
    experiment_nif.OrderedMap.Insts.RustlerTypesEncoder.encode value env =
      RustM.ok (.map [(.atom "low", .integer value.low.val), (.atom "high", .integer value.high.val)]) := by
  have distinct : Lynx.Rustler.Encoding.uniqueMapKeys [.atom "low", .atom "high"] = true := by
    simp [Lynx.Rustler.Encoding.uniqueMapKeys]
  simp [experiment_nif.OrderedMap.Insts.RustlerTypesEncoder.encode,
    experiment_nif.rustler_atoms_ordered_map.atom_low,
    experiment_nif.rustler_atoms_ordered_map.atom_high,
    RustWorkspace.MapDecodeFacade.RustlerAtomCache.cache_0,
    Lynx.Rustler.Encoding.atom, Lynx.Rustler.Encoding.u64,
    Lynx.Rustler.Encoding.mapFromTermArrays, distinct, Lynx.Rustler.Encoding.unwrapOk,
    Array.to_slice, Array.make, lift]

run_cmd do
  LynxTest.ProofAudit.checkModule `RustWorkspace.MapDecodeFacade.Funs
  LynxTest.ProofAudit.checkModule `RustWorkspace.NativeFormatting
  LynxTest.ProofAudit.checkModule `RustWorkspace.RustlerBridge
  LynxTest.ProofAudit.checkModule `RustWorkspace.DerivedMapDecoder
end RustWorkspace.DerivedMapDecoder
