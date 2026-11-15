open Aeneas Aeneas.Std Lynx atomic_nif
namespace Decoded.Boundary
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] def initial (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := NativeResourceArc.vmCells ({state := ⟨1⟩} : Counter) 2 3 4 ++
      [(1,NativeAtomic.typeName,NativeCodec.encode value)] }

/-- A failed decoder retires the temporary Rust owner. The complete heap,
including the VM pin and atomic value, is restored; fresh identities stay fresh. -/
theorem range_cleanup (dispatcher : Dispatcher) (value : U64) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_decoded/3» dispatcher (.nativeReference 4) (.integer (-1)) (.atom "true")).run
      (initial value) schedule =
        (.error (.error (.atom "badarg")), {initial value with nativeRefCounter := 5}) := by
  have rejected := Decoded.Properties.decoder_range (-1) (by decide)
  rw [Decoded.Properties.generic_decoder] at rejected
  simp [__NATIVE__.«atomic_decoded/3», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Decoded.Properties.reference_eq, rejected,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem panic_cleanup (dispatcher : Dispatcher) (value : U64) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_decoded/3» dispatcher (.nativeReference 4) (.integer 2) (.atom "true")).run
      (initial value) schedule =
        (.error (.error (.atom "nif_panicked")), {initial value with nativeRefCounter := 5}) := by
  have rejected := Decoded.Properties.decoder_panic
  rw [Decoded.Properties.generic_decoder] at rejected
  simp [__NATIVE__.«atomic_decoded/3», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Decoded.Properties.reference_eq, rejected,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem later_cleanup (dispatcher : Dispatcher) (value : U64) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_decoded/3» dispatcher (.nativeReference 4) (.integer 1) (.atom "invalid")).run
      (initial value) schedule =
        (.error (.error (.atom "badarg")), {initial value with nativeRefCounter := 5}) := by
  have accepted := Decoded.Properties.decoder_one
  rw [Decoded.Properties.generic_decoder] at accepted
  simp [__NATIVE__.«atomic_decoded/3», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Decoded.Properties.reference_eq, accepted, Rustler.decodeBool,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide
end Decoded.Boundary
