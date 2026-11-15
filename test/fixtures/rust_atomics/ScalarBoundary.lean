open Aeneas Aeneas.Std Lynx atomic_nif
namespace Scalars.Boundary
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] def initial (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := NativeResourceArc.vmCells ({state := ⟨1⟩} : Counter) 2 3 4 ++
      [(1, NativeAtomic.typeName, NativeCodec.encode value)] }

/-- A rejected derived request retires the temporary owner before error conversion,
including failures after an earlier field decoded successfully. -/
theorem request_rejection_cleanup (dispatcher : Dispatcher) (value : U64) (input : Term)
    (error : Rustler.DecoderError) (failure : Exception)
    (rejected : scalars.Request.Insts.RustlerTypesDecoder.decode input = NativeM.ok (.Err error))
    (converted : error.convert = .error failure) (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_scalar/2» dispatcher (.nativeReference 4) input).run
      (initial value) schedule =
      (.error failure, {initial value with nativeRefCounter := 5}) := by
  simp [__NATIVE__.«atomic_scalar/2», Rustler.withResourceTypes, Rustler.withNativeResult,
    initial, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Scalars.Properties.reference_eq, rejected, converted,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

end Scalars.Boundary
