open Aeneas Aeneas.Std Lynx atomic_nif
namespace Encoded.Boundary
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

@[expose] def initial (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := NativeResourceArc.vmCells ({state := ⟨1⟩} : Counter) 2 3 4 ++
      [(1, NativeAtomic.typeName, NativeCodec.encode value)] }

private theorem registry_self (label : String) : [label, label].eraseDups = [label] := by
  simp [List.eraseDups, List.eraseDupsBy, List.eraseDupsBy.loop]

private def cloned (previous : U64) : Environment :=
  { initial previous with
    nativeRefCounter := 5
    nativeHeap := [
      (5, NativeResourceArc.handleType Counter, .nativeReference 2),
      (4, NativeResourceArc.termType Counter, .tuple #[.nativeReference 2, .nativeReference 3]),
      (3, NativeResourceArc.handleType Counter, .nativeReference 2),
      (2, NativeResourceArc.typeName Counter, .tuple #[.integer 2, NativeCodec.encode ({state := ⟨1⟩} : Counter)]),
      (1, NativeAtomic.typeName, NativeCodec.encode previous)] }

private theorem decoded_prefix (previous : U64) (next : NativeResourceArc Counter → Result Term)
    (schedule : List ScheduleChoice) :
    (NativeResourceArc.decode (.nativeReference 4) >>= next).run (initial previous) schedule =
      (next ⟨2,5⟩).run (cloned previous) schedule := by
  simp [initial, cloned, NativeResourceArc.decode_eq, NativeResourceArc.clone,
    NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Encoded.Properties.reference_eq, Result.bind, Result.ofExcept]

private def encoded (owner : NativeResourceArc Counter) (previous : U64) : Result Term :=
  Rustler.executeNative (do
    let value ← __NATIVE__.«atomic_reply_checked:execution/3» owner previous 0#u64
    encoding.CheckedReply.Insts.RustlerTypesEncoder.encode value ()) id

private theorem encoded_run (previous : U64) (schedule : List ScheduleChoice) :
    (encoded ⟨2,5⟩ previous).run (cloned previous) schedule =
      (.error (.error (.atom "nif_panicked")), {initial 0#u64 with nativeRefCounter := 5}) := by
  simp [encoded, cloned, initial, __NATIVE__.«atomic_reply_checked:execution/3»,
    Encoded.Properties.facade_checked, Encoded.Properties.checked_spec,
    Rustler.executeNative, encoding.counter_reply, Encoded.Properties.composed,
    Encoded.Properties.contract, NativeResourceArc.vmCells, NativeResourceArc.ownership,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeResourceArc.deref, NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, Encoded.Properties.reference_eq,
    Result.handle, Result.bind, Result.ofExcept, List.filter_cons, List.filter_nil]

private def decoded_tail (owner : NativeResourceArc Counter) (previous : U64) : Result Term := do
  let expected ← Result.handle
    (Result.ofExcept (Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned previous)))
    (fun error => do NativeOwnedDrop.drop owner; Result.error error)
  let replacement ← Result.handle
    (Result.ofExcept (Rustler.decodeUnsigned .U64 64 (.integer 0)))
    (fun error => do NativeOwnedDrop.drop owner; Result.error error)
  Rustler.executeNative (do
    let value ← __NATIVE__.«atomic_reply_checked:execution/3» owner expected replacement
    encoding.CheckedReply.Insts.RustlerTypesEncoder.encode value ()) id

private theorem scalar_prefix (previous : U64) (next : U64 → U64 → Result Term)
    (handler : Exception → Result U64) :
    (do
      let expected ← Result.handle
        (Result.ofExcept (Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned previous))) handler
      let replacement ← Result.handle
        (Result.ofExcept (Rustler.decodeUnsigned .U64 64 (.integer 0))) handler
      next expected replacement) = next previous 0#u64 := by
  have decoded : Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned previous) = .ok previous := by
    exact Rustler.decodeUnsigned_encodeUnsigned previous
  have zero : Rustler.decodeUnsigned .U64 64 (.integer 0) = .ok 0#u64 := by
    exact Rustler.decodeUnsigned_encodeUnsigned 0#u64
  rw [decoded, zero]
  rfl

private theorem decoded_tail_eq (owner : NativeResourceArc Counter) (previous : U64) :
    decoded_tail owner previous = encoded owner previous := by
  exact scalar_prefix previous (fun expected replacement => Rustler.executeNative (do
    let value ← __NATIVE__.«atomic_reply_checked:execution/3» owner expected replacement
    encoding.CheckedReply.Insts.RustlerTypesEncoder.encode value ()) id)
    (fun error => do NativeOwnedDrop.drop owner; Result.error error)

private theorem wrapper_eq (dispatcher : Dispatcher) (previous : U64) :
    __NATIVE__.«atomic_reply_checked/3» dispatcher (.nativeReference 4)
      (Rustler.encodeUnsigned previous) (.integer 0) =
    Rustler.withResourceTypes [NativeResourceArc.typeName Counter]
      (NativeResourceArc.decode (.nativeReference 4) >>= fun owner => decoded_tail owner previous) := by
  unfold __NATIVE__.«atomic_reply_checked/3»
  rw [← Encoded.Properties.resource_tag]
  rfl

private theorem registered_run (computation : Result Term) (previous : U64)
    (schedule : List ScheduleChoice) :
    (Rustler.withResourceTypes [NativeResourceArc.typeName Counter] computation).run
      (initial previous) schedule = computation.run (initial previous) schedule := by
  simp only [Rustler.withResourceTypes, Result.nativeModify_run, initial,
    List.cons_append, List.nil_append, registry_self]

/-- An encoder panic occurs after the actual Rust update and owner release.
The full heap, VM pin and resource survive with the updated value. -/
theorem encoder_panic_cleanup (dispatcher : Dispatcher) (previous : U64)
    (schedule : List ScheduleChoice) :
    (__NATIVE__.«atomic_reply_checked/3» dispatcher (.nativeReference 4)
      (Rustler.encodeUnsigned previous) (.integer 0)).run (initial previous) schedule =
      (.error (.error (.atom "nif_panicked")), {initial 0#u64 with nativeRefCounter := 5}) := by
  rw [wrapper_eq, registered_run, decoded_prefix, decoded_tail_eq]
  exact encoded_run previous schedule

end Encoded.Boundary
