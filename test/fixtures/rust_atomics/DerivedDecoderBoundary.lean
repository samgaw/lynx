open Aeneas Aeneas.Std Lynx atomic_nif
namespace Derived.Boundary
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] def initial (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := NativeResourceArc.vmCells ({state := ⟨1⟩} : Counter) 2 3 4 ++
      [(1,NativeAtomic.typeName,NativeCodec.encode value)] }

/-- A failed decoder retires the temporary Rust owner. The complete heap,
including the VM pin and atomic value, is restored; fresh identities stay fresh. -/
theorem non_tuple_cleanup (dispatcher : Dispatcher) (value : U64) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_tuple/2» dispatcher (.nativeReference 4) (.integer 7)).run
      (initial value) schedule =
        (.error (.error (.atom "badarg")), {initial value with nativeRefCounter := 5}) := by
  have rejected := Derived.Properties.non_tuple (.integer 7) (by intro fields; intro h; cases h)
  simp [__NATIVE__.«atomic_tuple/2», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Derived.Properties.reference_eq, rejected,
    Rustler.badArgOutcome, Rustler.DecoderError.convert,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem expected_cleanup (dispatcher : Dispatcher) (value : U64) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_tuple/2» dispatcher (.nativeReference 4) (.tuple #[.atom "false", .integer 11])).run
      (initial value) schedule =
        (.error (.error (.bitstring "Could not decode field expected on Request".toUTF8 0)), {initial value with nativeRefCounter := 5}) := by
  have rejected := Derived.Properties.decoder_expected_error (.atom "false") (.integer 11) (by rfl)
  have size : "Could not decode field expected on Request".utf8ByteSize ≤ 4294967295 := by decide +kernel
  simp [__NATIVE__.«atomic_tuple/2», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Derived.Properties.reference_eq, rejected,
    Rustler.badArgOutcome, Rustler.DecoderError.convert, Rustler.raiseTermErrorOutcome, Rustler.Encoding.string, size,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem replacement_cleanup (dispatcher : Dispatcher) (value : U64) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_tuple/2» dispatcher (.nativeReference 4) (.tuple #[Rustler.encodeUnsigned 7#u64, .integer (-1)])).run
      (initial value) schedule =
        (.error (.error (.bitstring "Could not decode field replacement on Request".toUTF8 0)), {initial value with nativeRefCounter := 5}) := by
  have rejected := Derived.Properties.decoder_replacement_error 7#u64 (.integer (-1)) (by rfl)
  have size : "Could not decode field replacement on Request".utf8ByteSize ≤ 4294967295 := by decide +kernel
  simp [__NATIVE__.«atomic_tuple/2», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Derived.Properties.reference_eq, rejected,
    Rustler.badArgOutcome, Rustler.DecoderError.convert, Rustler.raiseTermErrorOutcome, Rustler.Encoding.string, size,
    atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

end Derived.Boundary
