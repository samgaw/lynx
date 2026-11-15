theorem resource_tag : NativeResourceArc.typeName Counter = __RESOURCE_TYPE__ := by rfl


theorem facade_new (value : U64) : __NEW__ value = counter_new value := by rfl

theorem facade_read (owner : NativeResourceArc Counter) :
    __READ__ owner = counter_read owner := by rfl

theorem facade_reply (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __REPLY__ owner expected replacement = encoding.counter_reply owner expected replacement := by rfl

theorem facade_optional (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __OPTION__ owner expected replacement = (do
      let response ← encoding.counter_reply owner expected replacement
      if response.current = 0#u64 then NativeM.ok none
      else NativeM.ok (some {value := response.current})) := by rfl

theorem facade_result (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __RESULT__ owner expected replacement = (do
      let response ← encoding.counter_reply owner expected replacement
      if response.previous = expected then NativeM.ok (.Ok response)
      else NativeM.ok (.Err response.previous)) := by rfl

theorem facade_tuple (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __TUPLE__ owner expected replacement = (do
      let response ← encoding.counter_reply owner expected replacement
      NativeM.ok (response, response.current)) := by rfl

theorem facade_checked (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __CHECKED__ owner expected replacement = (do
      let response ← encoding.counter_reply owner expected replacement
      NativeM.ok {value := response.current}) := by rfl

theorem facade_returned (owner : NativeResourceArc Counter) (expected replacement : U64) :
    __RETURNED__ owner expected replacement = (do
      if expected = core.num.U64.MAX then
        NativeOwnedDrop.drop owner
        NativeM.ok (.Err Encoded.Extraction.ErrorConstants.literal_0)
      else
        let response ← encoding.counter_reply owner expected replacement
        NativeM.ok (.Ok response)) := by rfl

theorem returned_error_cleanup (previous replacement : U64) (schedule : List ScheduleChoice) :
    (__RETURNED__ ⟨2,3⟩ core.num.U64.MAX replacement).run (retained previous) schedule =
      (.ok (.Err (Rustler.raiseAtomErrorOutcome "rust_panicked")), afterCall previous) := by
  simp [facade_returned, retained, afterCall, Encoded.Extraction.ErrorConstants.literal_0,
    NativeResourceArc.releaseOwned, NativeResourceArc.ownedState, NativeResourceArc.ownerState,
    NativeResourceArc.ownership, NativeResourceArc.retiredState,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.referenceLimit,
    NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeOwnedDrop.drop, NativeAtomic.typeName, NativeCodec.roundtrip, reference_eq,
    NativeM.ok, NativeM.fail, NativeM.lift, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
