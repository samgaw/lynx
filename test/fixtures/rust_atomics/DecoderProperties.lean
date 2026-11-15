module
public import Decoded.Extraction.Funs
public import Decoded.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Decoded.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem generic_decoder (term : Term) :
    decoding.decode_request term = decoding.Request.Insts.RustlerTypesDecoder.decode term := by rfl

theorem decoder_error (term : Term) (error : Exception)
    (rejected : Rustler.decodeUnsigned .U64 64 term = .error error) :
    decoding.decode_request term = .ok (.Err (.error error)) := by
  simp [generic_decoder, decoding.Request.Insts.RustlerTypesDecoder.decode,
    decoding.decode_via, U64.Insts.RustlerTypesDecoder, Rustler.NativeDecoding.u64,
    Rustler.Decoding.u64, rejected, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem decoder_range (value : Int) (outside : ¬ (0 ≤ value ∧ value < 2^64)) :
    decoding.decode_request (.integer value) = .ok (.Err (.error (.error (.atom "badarg")))) := by
  exact decoder_error _ _ (Rustler.decodeUnsigned_outOfRange .U64 64 value outside)

theorem decoder_zero :
    decoding.decode_request (.integer 0) = .ok (.Ok ⟨0#u64⟩) := by rfl

theorem decoder_one :
    decoding.decode_request (.integer 1) = .ok (.Ok ⟨1#u64⟩) := by rfl

theorem decoder_panic :
    decoding.decode_request (.integer 2) = .error (.error (.atom "rust_panicked")) := by rfl

theorem decoder_marker :
    decoding.decode_request (.integer 3) = .ok (.Err (Rustler.raiseAtomErrorOutcome "rust_panicked")) := by rfl

theorem decoder_atom :
    decoding.decode_request (.integer 4) = .ok (.Err (Rustler.atomErrorOutcome "decoder_rejected")) := by rfl

theorem decoder_badarg :
    decoding.decode_request (.integer 5) = .ok (.Err Rustler.badArgOutcome) := by rfl

theorem claim_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_core.claim counter = NativeAtomic.fetchAdd counter 1#u64 .SeqCst := by rfl

theorem current_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_core.current counter = NativeAtomic.load counter .SeqCst := by rfl

theorem two_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_analysis.claim_two counter = (do
      let first ← atomic_core.claim counter
      let second ← atomic_core.claim counter
      NativeM.ok (first,second)) := by rfl

theorem disabled_contract (owner : NativeResourceArc Counter) (request : decoding.Request) :
    decoding.counter_decoded owner request false = (do
      let counter ← NativeResourceArc.deref owner
      let value ← atomic_core.current counter.state
      NativeOwnedDrop.drop owner
      NativeM.ok value) := by
  simp [decoding.counter_decoded]

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

theorem enabled_updates (value : U64) (schedule : List ScheduleChoice) :
    (decoding.counter_decoded ⟨2,3⟩ ⟨1#u64⟩ true).run (retained value) schedule =
      (.ok value, afterCall (NativeAtomic.wrappingAdd (NativeAtomic.wrappingAdd value 1#u64) 1#u64)) := by
  dsimp only [decoding.counter_decoded, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [two_contract, claim_contract, current_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.load, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem disabled_preserves (value : U64) (request : decoding.Request) (schedule : List ScheduleChoice) :
    (decoding.counter_decoded ⟨2,3⟩ request false).run (retained value) schedule =
      (.ok value, afterCall value) := by
  rw [disabled_contract]
  simp [current_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.load, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide
end Decoded.Properties
