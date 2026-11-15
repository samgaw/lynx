module
public import Atomic.Returned.Funs
public import Atomic.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Atomic.ReturnedProperties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem native_ok (value : U64) (next : U64 → Result Term) :
    Rustler.withNativeResult (.ok (.Ok value)) next = next value := by rfl

theorem returned_badarg :
    Rustler.withNativeResult (.ok (.Err Rustler.badArgOutcome) : Result (core.result.Result U64 Rustler.DecoderError))
      (fun value => .ok (Rustler.encodeUnsigned value)) = .error (.error (.atom "badarg")) := by rfl

theorem explicit_marker :
    Rustler.withNativeResult (.ok (.Err (Rustler.raiseAtomErrorOutcome "rust_panicked")) :
      Result (core.result.Result U64 Rustler.DecoderError))
      (fun value => .ok (Rustler.encodeUnsigned value)) = .error (.error (.atom "rust_panicked")) := by rfl

theorem native_panic :
    Rustler.withNativeResult (.error (.error (.atom "rust_panicked")) :
      Result (core.result.Result U64 Rustler.DecoderError))
      (fun value => .ok (Rustler.encodeUnsigned value)) = .error (.error (.atom "nif_panicked")) := by rfl

theorem no_catch_continuation (value : U64) :
    Rustler.withNativeResult (.ok (.Ok value))
      (fun _ => .error (.error (.atom "rust_panicked"))) = .error (.error (.atom "rust_panicked")) := by rfl

theorem cutoff :
    Rustler.withNativeResult (.error .exhausted : Result (core.result.Result U64 Rustler.DecoderError))
      (fun value => .ok (Rustler.encodeUnsigned value)) = .error .exhausted := by rfl

theorem claim_contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) :
    atomic_core.claim counter = NativeAtomic.fetchAdd counter 1#u64 .SeqCst := by rfl

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
      (1,NativeAtomic.typeName,NativeCodec.encode (NativeAtomic.wrappingAdd value 1#u64))] }

/-- The actual Rust code updates before constructing BadArg, and releases only
its consumed owner. The other owner and updated counter survive the error. -/
theorem badarg_after_update (value : U64) (schedule : List ScheduleChoice) :
    (counter_result ⟨2,3⟩ 1#u64).run (retained value) schedule =
      (.ok (.Ok (.Err Rustler.badArgOutcome)), afterCall value) := by
  dsimp only [counter_result, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [claim_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop,
    NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem ok_after_update (value : U64) (schedule : List ScheduleChoice) :
    (counter_result ⟨2,3⟩ 0#u64).run (retained value) schedule =
      (.ok (.Ok (.Ok value)), afterCall value) := by
  dsimp only [counter_result, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [claim_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop,
    NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem atom_after_update (value : U64) (schedule : List ScheduleChoice) :
    (counter_result ⟨2,3⟩ 2#u64).run (retained value) schedule =
      (.ok (.Ok (.Err Atomic.Returned.ErrorConstants.literal_0)), afterCall value) := by
  dsimp only [counter_result, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [claim_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop,
    NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem marker_after_update (value : U64) (schedule : List ScheduleChoice) :
    (counter_result ⟨2,3⟩ 3#u64).run (retained value) schedule =
      (.ok (.Ok (.Err Atomic.Returned.ErrorConstants.literal_1)), afterCall value) := by
  dsimp only [counter_result, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [claim_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop,
    NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem panic_after_update (value : U64) (schedule : List ScheduleChoice) :
    (counter_result ⟨2,3⟩ 4#u64).run (retained value) schedule =
      (.ok (.Err ()), afterCall value) := by
  dsimp only [counter_result, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [claim_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop,
    NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem denied_after_update (value : U64) (schedule : List ScheduleChoice) :
    (counter_result ⟨2,3⟩ 5#u64).run (retained value) schedule =
      (.ok (.Ok (.Err Atomic.Returned.ErrorConstants.literal_2)), afterCall value) := by
  dsimp only [counter_result, U64.ofNat, UScalar.ofNat, UScalar.ofNatCore]
  simp [claim_contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.fetchAdd, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeResourceUnwindDrop.drop, NativeOwnedDrop.drop,
    NativeM.ok, NativeM.fail, NativeM.lift, NativeCodec.roundtrip, reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide
end Atomic.ReturnedProperties
