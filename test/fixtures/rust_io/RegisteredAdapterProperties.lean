module
public import Record.RegisteredLogProperties
public import Record.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.RegisteredAdapterProperties
open NativeFile Record.Properties Record.CrashProperties Record.AppendProperties Record.RecoveryProperties
  Record.LockedProperties Record.NativeLogProperties Record.ScheduledLogProperties
set_option maxRecDepth 4096
attribute [local simp] NativeCodec.typeName NativeResourceArc.typeName NativeMutex.typeName NativeFile.typeName

@[expose] def resourceTypes : List String := [NativeResourceArc.typeName shared_log.LogResource]
@[expose] def recordValue (first : Bool) : U16 := if first then 13#u16 else 19#u16

/-- The compiled wrapper executes registration, both decoders, the actual Rust
facade and its result/exception adapter. No predecoded owner is supplied. -/
theorem adapter_steps (pid : PID) (first : Bool) (available : List String)
    (same : (available ++ resourceTypes).eraseDups = resourceTypes)
    (before sought written committed : State) (position : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought)
    (valid2 : Record.Properties.Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload (recordValue first)) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.RegisteredSteps pid
      (Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0)
        (.nativeReference 6) (.integer (if first then 13 else 19)))
      (shared (Record.RegisteredLogProperties.counter first - 1) pinnedFrame (Record.FramedLogProperties.free false) before)
      available Term.true
      (shared (Record.RegisteredLogProperties.counter first + 1) pinnedFrame (Record.FramedLogProperties.free false) committed) resourceTypes := by
  have decoded := Record.RegisteredLogProperties.decoded_call_steps pid first resourceTypes
    (by simp [resourceTypes]) before sought written committed (recordValue first) position
    valid0 valid1 valid2 ready0 ready1 ready2 seek write sync
  have registered := Rustler.withResourceTypes_registeredSteps available resourceTypes resourceTypes
    (by simpa only [same] using decoded)
  cases first <;>
    simpa [Elixir.LynxIoFixture.Native.«log_append/2»,
      Elixir.LynxIoFixture.Native.«log_append:execution/2», resourceTypes, recordValue,
      Rustler.decodeUnsigned, Result.ofExcept, Result.handle, shared,
      Record.RegisteredLogProperties.shared, UScalar.ofNat, UScalar.ofNatCore,
      BitVec.ofFin_eq_ofNat] using registered

theorem adapter_calls (before sought1 written1 committed1 sought2 written2 committed2 : State)
    (position1 position2 : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought1)
    (valid2 : Record.Properties.Valid written1) (valid3 : Record.Properties.Valid committed1)
    (valid4 : Record.Properties.Valid sought2) (valid5 : Record.Properties.Valid written2)
    (ready0 : blocked before = false) (ready1 : blocked sought1 = false) (ready2 : blocked written1 = false)
    (ready3 : blocked committed1 = false) (ready4 : blocked sought2 = false) (ready5 : blocked written2 = false)
    (seek1 : seekStep before (.end_ 0#i64) = some (.Ok position1, sought1))
    (write1 : writeStep sought1 (payload 13#u16) = some (.Ok 4#usize, written1))
    (sync1 : syncStep written1 = some (.Ok (), committed1))
    (seek2 : seekStep committed1 (.end_ 0#i64) = some (.Ok position2, sought2))
    (write2 : writeStep sought2 (payload 19#u16) = some (.Ok 4#usize, written2))
    (sync2 : syncStep written2 = some (.Ok (), committed2)) :
    let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.nativeReference 6) (.integer 13)
    let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.nativeReference 6) (.integer 19)
    (Result.schedule {} child (fun _ => parent))
      {nativeRefCounter := 6, nativeHeap := (shared 6 pinnedFrame (Record.FramedLogProperties.free false) before).2} =
      (.ok Term.true, {
        nativeRefCounter := 10, nativeResourceTypes := resourceTypes,
        nativeHeap := (shared 10 pinnedFrame (Record.FramedLogProperties.free false) committed2).2}) := by
  dsimp only
  have parent := adapter_steps [] true [] rfl before sought1 written1 committed1 position1
    valid0 valid1 valid2 ready0 ready1 ready2 seek1 write1 sync1
  have child := adapter_steps [1] false resourceTypes (by simp [resourceTypes, List.eraseDups_cons])
    committed1 sought2 written2 committed2 position2
    valid3 valid4 valid5 ready3 ready4 ready5 seek2 write2 sync2
  simpa [Record.RegisteredLogProperties.counter, shared, resourceTypes] using
    Result.two_registered_serial_steps _ _ _ _ _ _ _ _ _ _ parent child

theorem registered_records :
    let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.nativeReference 6) (.integer 13)
    let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.nativeReference 6) (.integer 19)
    (Result.schedule {} child (fun _ => parent))
      {nativeRefCounter := 6, nativeHeap := (shared 6 pinnedFrame (Record.FramedLogProperties.free false) firstInput).2} =
      (.ok Term.true, {
        nativeRefCounter := 10, nativeResourceTypes := resourceTypes,
        nativeHeap := (shared 10 pinnedFrame (Record.FramedLogProperties.free false) complete).2}) := by
  have bytes13 : (bytes (payload 13#u16)).size = 4 := by
    simp [bytes_size, payload, Record.IntegrityProperties.layout]
  have bytes19 : (bytes (payload 19#u16)).size = 4 := by
    simp [bytes_size, payload, Record.IntegrityProperties.layout]
  have firstSize : firstBytes.size = 4 := by
    simp [firstBytes, overwrite_size _ _ _ _ (by omega : 4 ≤ (bytes (payload 13#u16)).size)]
  have bothSize : bothBytes.size = 8 := by
    simp [bothBytes, overwrite_size _ _ _ _ (by omega : 4 ≤ (bytes (payload 19#u16)).size), firstSize]
  have validFirstWrite : Record.Properties.Valid firstWrite := by
    change firstBytes.size ≤ limit ∧ 0 ≤ firstBytes.size ∧ 4 ≤ limit
    simp [firstSize, limit]
  have validSecondWrite : Record.Properties.Valid secondWrite := by
    change bothBytes.size ≤ limit ∧ firstBytes.size ≤ bothBytes.size ∧ 8 ≤ limit
    simp [firstSize, bothSize, limit]
  simpa using adapter_calls firstInput firstSeek firstWrite secondInput secondSeek secondWrite complete
    0#u64 4#u64
    (by unfold Record.Properties.Valid; decide) (by unfold Record.Properties.Valid; decide)
    validFirstWrite (by simp [Record.Properties.Valid, secondInput, appendInput, firstSize, limit])
    (by simp [Record.Properties.Valid, secondSeek, sought, secondInput, appendInput, firstSize, limit])
    validSecondWrite
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by rfl) (by rfl) (by rfl)
    (by
      have valid : Record.Properties.Valid secondInput := by
        simp [Record.Properties.Valid, secondInput, appendInput, firstSize, limit]
      simpa [secondInput, appendInput, secondSeek, firstSize, U64.ofNatCore] using
        seek_end_step secondInput valid (zeroMask firstBytes) firstBytes _
          (action_outcome _ _ _ _ _) (persist_zero firstBytes))
    (by
      have kept : persist secondSeek.durable
          (overwrite secondSeek.visible secondSeek.position (bytes (payload 19#u16)) 4)
          (zeroMask firstBytes) = some firstBytes := by
        simpa [secondSeek, sought, secondInput, appendInput] using
          Record.ResizeProperties.persist_keep_old firstBytes
            (overwrite firstBytes 4 (bytes (payload 19#u16)) 4)
      simpa [secondWrite, Record.Properties.count, Usize.ofNatCore, UScalar.ofNat] using
        write_step secondSeek (payload 19#u16) 4 (zeroMask firstBytes) firstBytes _
          (by simp [payload, Record.IntegrityProperties.layout])
          (by simp [payload, Record.IntegrityProperties.layout, limit])
          (by simp [secondSeek, sought, limit]) (action_outcome _ _ _ _ _) kept)
    (by rfl)


end Record.RegisteredAdapterProperties
