module
public import Record.ConstructedConcurrentProperties
public import Record.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConstructedContendedProperties
open NativeFile Record.Properties Record.CrashProperties Record.AppendProperties Record.RecoveryProperties
  Record.LockedProperties Record.ConstructedConcurrentProperties
open Record.ScheduledLogProperties (firstInput firstSeek firstWrite secondInput secondSeek secondWrite complete firstBytes bothBytes)
@[expose] def resourceTypes : List String := [NativeResourceArc.typeName shared_log.LogResource]
@[expose] def recordValue (first : Bool) : U16 := if first then 13#u16 else 19#u16
set_option maxRecDepth 4096
attribute [local simp] NativeCodec.encode NativeCodec.typeName NativeResourceArc.typeName NativeMutex.typeName NativeFile.typeName

/-- The generated wrapper stops at its real lock wait, after registration,
argument conversion and the actual Rust borrow. -/
theorem adapter_prefix (pid : PID) (first : Bool) (available : List String)
    (same : (available ++ resourceTypes).eraseDups = resourceTypes)
    (contents : Term) (state : State) :
    Result.RegisteredPrefix pid
      (Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0)
        (.reference 8) (.integer (if first then 13 else 19)))
      (shared (beforeCounter first) (beforeFrame first) contents state) available
      (.wait (NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile)) (resume first (recordValue first)))
      (shared (beforeCounter first + 1) (decodedOwners first) contents state) resourceTypes := by
  have decoded := decoded_lock_prefix pid first resourceTypes (by simp [resourceTypes]) contents state (recordValue first)
  have registered := Rustler.withResourceTypes_registeredPrefix available resourceTypes resourceTypes
    (by simpa only [same] using decoded)
  cases first <;>
    simpa [Elixir.LynxIoFixture.Native.«log_append/2»,
      Elixir.LynxIoFixture.Native.«log_append:execution/2», resourceTypes, recordValue,
      Rustler.decodeUnsigned, Result.ofExcept, Result.handle, UScalar.ofNat, UScalar.ofNatCore,
      BitVec.ofFin_eq_ofNat] using registered

theorem contended_calls (before sought1 written1 committed1 sought2 written2 committed2 : State)
    (position1 position2 : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought1)
    (valid2 : Record.Properties.Valid written1) (valid3 : Record.Properties.Valid committed1)
    (valid4 : Record.Properties.Valid sought2) (valid5 : Record.Properties.Valid written2)
    (ready0 : blocked before = false) (ready1 : blocked sought1 = false) (ready2 : blocked written1 = false)
    (ready3 : blocked committed1 = false) (ready4 : blocked sought2 = false) (ready5 : blocked written2 = false)
    (seek1 : seekStep before (.end_ 0#i64) = some (.Ok position1, sought1))
    (write1 : writeStep sought1 (Record.CrashProperties.payload 13#u16) = some (.Ok 4#usize, written1))
    (sync1 : syncStep written1 = some (.Ok (), committed1))
    (seek2 : seekStep committed1 (.end_ 0#i64) = some (.Ok position2, sought2))
    (write2 : writeStep sought2 (Record.CrashProperties.payload 19#u16) = some (.Ok 4#usize, written2))
    (sync2 : syncStep written2 = some (.Ok (), committed2)) :
    let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 8) (.integer 13)
    let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 8) (.integer 19)
    (Result.schedule child (fun _ => parent))
      {refCounter := 8, nativeHeap := (shared 8 .pinned (free) before).2,
        nativeResourceTypes := resourceTypes, schedule := [.current, .swap 2]} =
      (.ok Term.true, {
        pidCounter := 2, refCounter := 12, nativeResourceTypes := resourceTypes,
        nativeHeap := (shared 12 .pinned (free) committed2).2}) := by
  dsimp only
  let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 8) (.integer 13)
  let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 8) (.integer 19)
  obtain ⟨childRead, childEq⟩ : ∃ read : Environment → Result Term, child = .get read := ⟨_, rfl⟩
  let held1 := NativeMutex.lockedContents 1 10 false (⟨2⟩ : NativeFile)
  let held2 := NativeMutex.lockedContents 2 12 false (⟨2⟩ : NativeFile)
  let guard1 : NativeGuard NativeFile := ⟨⟨4⟩, 10, 1, ⟨2⟩⟩
  let guard2 : NativeGuard NativeFile := ⟨⟨4⟩, 12, 2, ⟨2⟩⟩
  have parentPrefix := adapter_prefix 1 true resourceTypes (by simp [resourceTypes,List.eraseDups_cons]) free before
  have childPrefix := adapter_prefix 2 false resourceTypes
    (by simp [resourceTypes, List.eraseDups_cons]) held1 before
  change Result.RegisteredPrefix 2 child _ _ _ _ _ at childPrefix
  rw [childEq] at childPrefix
  have parentTrace := Rustler.executeNative_sharedSteps
    (Record.ConstructedConcurrentProperties.body_steps 1 true 11 10 (by decide)
      before sought1 written1 committed1 13#u16 position1
      valid0 valid1 valid2 ready0 ready1 ready2 seek1 write1 sync1) Rustler.encodeBool
  have childTrace := Rustler.executeNative_sharedSteps
    (Record.ConstructedConcurrentProperties.body_steps 2 false 12 12 (by decide)
      committed1 sought2 written2 committed2 19#u16 position2
      valid3 valid4 valid5 ready3 ready4 ready5 seek2 write2 sync2) Rustler.encodeBool
  have run := Result.two_registered_interleave_steps parent childRead
    (NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile)) (resume true 13#u16)
    (NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile)) (resume false 19#u16)
    (.ok (.Ok guard1)) (.ok (.Ok guard2)) Term.true Term.true
    (shared 8 .pinned free before) (shared 9 .decoded free before)
    (shared 10 .decoded held1 before) (shared 11 .overlapping held1 before)
    (shared 11 .remaining free committed1) (shared 12 .remaining held2 committed1)
    (shared 12 .pinned free committed2) resourceTypes resourceTypes resourceTypes
    (by simpa [parent, beforeCounter, beforeFrame, decodedOwners, recordValue] using parentPrefix)
    (by simpa [beforeCounter, beforeFrame, decodedOwners, recordValue] using childPrefix)
    ?_ ?_ ?_ ?_ ?_
  · simpa [parent, ← childEq, child, free, shared] using run
  · have acquired := Record.ConstructedConcurrentProperties.lock_poll
      ({pidCounter := 2, processes := [(2,{})], nativeResourceTypes := resourceTypes,
        schedule := [.swap 2]} : Environment) 9 .decoded before
      (by simp [shared,frame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells])
    simpa [guard1, free, held1, shared, world,frame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells] using acquired
  · simpa [resume, resource, beforeCounter, guard1, held1, free,
      Record.ConstructedConcurrentProperties.owner, bodyPhase, afterPhase, Rustler.encodeBool, recoverGuard] using parentTrace
  · simp [NativeMutex.pollLock, shared, overlappingFrame, decodedFrame, pinnedFrame,frame,
      NativeResourceArc.vmCells, held1, NativeMutex.lockedContents, NativeCodec.decode]
  · have acquired := Record.ConstructedConcurrentProperties.lock_poll
      ({currentPid := 2, pidCounter := 2, nativeResourceTypes := resourceTypes} : Environment)
      11 .remaining committed1
      (by simp [shared,frame,remainingFrame,overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells])
    simpa [guard2, free, held2, shared, world,frame,remainingFrame,overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells] using acquired
  · simpa [resume, resource, beforeCounter, guard2, held2, free,
      Record.ConstructedConcurrentProperties.owner, bodyPhase, afterPhase, Rustler.encodeBool, recoverGuard] using childTrace

theorem contended_records :
    let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 8) (.integer 13)
    let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 8) (.integer 19)
    (Result.schedule child (fun _ => parent))
      {refCounter := 8, nativeHeap := (shared 8 .pinned (free) firstInput).2,
        nativeResourceTypes := resourceTypes, schedule := [.current, .swap 2]} =
      (.ok Term.true, {
        pidCounter := 2, refCounter := 12, nativeResourceTypes := resourceTypes,
        nativeHeap := (shared 12 .pinned (free) complete).2}) := by
  have bytes13 : (bytes (Record.CrashProperties.payload 13#u16)).size = 4 := by
    simp [bytes_size, Record.CrashProperties.payload, Record.IntegrityProperties.layout]
  have bytes19 : (bytes (Record.CrashProperties.payload 19#u16)).size = 4 := by
    simp [bytes_size, Record.CrashProperties.payload, Record.IntegrityProperties.layout]
  have firstSize : firstBytes.size = 4 := by
    simp [firstBytes, overwrite_size _ _ _ _ (by omega : 4 ≤ (bytes (Record.CrashProperties.payload 13#u16)).size)]
  have bothSize : bothBytes.size = 8 := by
    simp [bothBytes, overwrite_size _ _ _ _ (by omega : 4 ≤ (bytes (Record.CrashProperties.payload 19#u16)).size), firstSize]
  have validFirstWrite : Record.Properties.Valid firstWrite := by
    change firstBytes.size ≤ limit ∧ 0 ≤ firstBytes.size ∧ 4 ≤ limit
    simp [firstSize, limit]
  have validSecondWrite : Record.Properties.Valid secondWrite := by
    change bothBytes.size ≤ limit ∧ firstBytes.size ≤ bothBytes.size ∧ 8 ≤ limit
    simp [firstSize, bothSize, limit]
  simpa using contended_calls firstInput firstSeek firstWrite secondInput secondSeek secondWrite complete
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
          (overwrite secondSeek.visible secondSeek.position (bytes (Record.CrashProperties.payload 19#u16)) 4)
          (zeroMask firstBytes) = some firstBytes := by
        simpa [secondSeek, sought, secondInput, appendInput] using
          Record.ResizeProperties.persist_keep_old firstBytes
            (overwrite firstBytes 4 (bytes (Record.CrashProperties.payload 19#u16)) 4)
      simpa [secondWrite, Record.Properties.count, Usize.ofNatCore, UScalar.ofNat] using
        write_step secondSeek (Record.CrashProperties.payload 19#u16) 4 (zeroMask firstBytes) firstBytes _
          (by simp [Record.CrashProperties.payload, Record.IntegrityProperties.layout])
          (by simp [Record.CrashProperties.payload, Record.IntegrityProperties.layout, limit])
          (by simp [secondSeek, sought, limit]) (action_outcome _ _ _ _ _) kept)
    (by rfl)


/-- The resource in the contended run is created by the actual exported
constructor, starting with only a namespace and successful host outcomes. -/
theorem created_contended_records :
    (do
      let resource ← Elixir.LynxIoFixture.Native.«log_create/0» (Dispatcher.ofTable #[] 0)
      Result.schedule
        (Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) resource (.integer 19))
        (fun _ => Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) resource (.integer 13)))
      (Record.ConstructorLogProperties.initial {schedule := [.current, .swap 2]} firstInput.script) =
      (.ok Term.true, {
        pidCounter := 2, refCounter := 12, nativeResourceTypes := resourceTypes,
        nativeHeap := (shared 12 .pinned free complete).2}) := by
  rw [Record.ConstructorAdapterProperties.create_next]
  rw [constructed_shape]
  simpa [world,Record.ConstructorAdapterProperties.registered,resourceTypes,
    Record.ScheduledLogProperties.firstInput,Record.LockedProperties.appendInput,List.eraseDups_cons] using contended_records

end Record.ConstructedContendedProperties
