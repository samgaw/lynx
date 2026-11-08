module
public import Record.ContendedLogProperties
public import Record.RegisteredAdapterProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ContendedAdapterProperties
open NativeFile Record.Properties Record.CrashProperties Record.AppendProperties Record.RecoveryProperties
  Record.LockedProperties Record.NativeLogProperties Record.OverlappingLogProperties
  Record.ScheduledLogProperties Record.ContendedLogProperties
open Record.RegisteredAdapterProperties (resourceTypes recordValue)
set_option maxRecDepth 4096
attribute [local simp] NativeCodec.encode NativeCodec.typeName NativeResourceArc.typeName NativeMutex.typeName NativeFile.typeName

/-- The generated wrapper stops at its real lock wait, after registration,
argument conversion and the actual Rust borrow. -/
theorem adapter_prefix (pid : PID) (first : Bool) (available : List String)
    (same : (available ++ resourceTypes).eraseDups = resourceTypes)
    (contents : Term) (state : State) :
    Result.RegisteredPrefix pid
      (Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0)
        (.reference 6) (.integer (if first then 13 else 19)))
      (shared (beforeCounter first) (beforeFrame first) contents state) available
      (.wait (NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile)) (resume first (recordValue first)))
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
    (write1 : writeStep sought1 (payload 13#u16) = some (.Ok 4#usize, written1))
    (sync1 : syncStep written1 = some (.Ok (), committed1))
    (seek2 : seekStep committed1 (.end_ 0#i64) = some (.Ok position2, sought2))
    (write2 : writeStep sought2 (payload 19#u16) = some (.Ok 4#usize, written2))
    (sync2 : syncStep written2 = some (.Ok (), committed2)) :
    let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 6) (.integer 13)
    let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 6) (.integer 19)
    (Result.schedule child (fun _ => parent))
      {refCounter := 6, nativeHeap := (shared 6 pinnedFrame (Record.FramedLogProperties.free false) before).2,
        schedule := [.current, .swap 2]} =
      (.ok Term.true, {
        pidCounter := 2, refCounter := 10, nativeResourceTypes := resourceTypes,
        nativeHeap := (shared 10 pinnedFrame (Record.FramedLogProperties.free false) committed2).2}) := by
  dsimp only
  let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 6) (.integer 13)
  let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 6) (.integer 19)
  obtain ⟨childRead, childEq⟩ : ∃ read : Environment → Result Term, child = .get read := ⟨_, rfl⟩
  let free := Record.FramedLogProperties.free false
  let held1 := NativeMutex.lockedContents 1 8 false (⟨2⟩ : NativeFile)
  let held2 := NativeMutex.lockedContents 2 10 false (⟨2⟩ : NativeFile)
  let guard1 : NativeGuard NativeFile := ⟨⟨1⟩, 8, 1, ⟨2⟩⟩
  let guard2 : NativeGuard NativeFile := ⟨⟨1⟩, 10, 2, ⟨2⟩⟩
  have parentPrefix := adapter_prefix 1 true [] rfl free before
  have childPrefix := adapter_prefix 2 false resourceTypes
    (by simp [resourceTypes, List.eraseDups_cons]) held1 before
  change Result.RegisteredPrefix 2 child _ _ _ _ _ at childPrefix
  rw [childEq] at childPrefix
  have parentTrace := Rustler.executeNative_sharedSteps
    (Record.ScheduledLogProperties.body_steps 1 true 9 8 (by decide)
      before sought1 written1 committed1 13#u16 position1
      valid0 valid1 valid2 ready0 ready1 ready2 seek1 write1 sync1) Rustler.encodeBool
  have childTrace := Rustler.executeNative_sharedSteps
    (Record.ScheduledLogProperties.body_steps 2 false 10 10 (by decide)
      committed1 sought2 written2 committed2 19#u16 position2
      valid3 valid4 valid5 ready3 ready4 ready5 seek2 write2 sync2) Rustler.encodeBool
  have run := Result.two_registered_interleave_steps parent childRead
    (NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile)) (resume true 13#u16)
    (NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile)) (resume false 19#u16)
    (.ok (.Ok guard1)) (.ok (.Ok guard2)) Term.true Term.true
    (shared 6 pinnedFrame free before) (shared 7 decodedFrame free before)
    (shared 8 decodedFrame held1 before) (shared 9 overlappingFrame held1 before)
    (shared 9 afterFirstFrame free committed1) (shared 10 afterFirstFrame held2 committed1)
    (shared 10 pinnedFrame free committed2) [] resourceTypes resourceTypes
    (by simpa [parent, beforeCounter, beforeFrame, decodedOwners, recordValue] using parentPrefix)
    (by simpa [beforeCounter, beforeFrame, decodedOwners, recordValue] using childPrefix)
    ?_ ?_ ?_ ?_ ?_
  · simpa [parent, ← childEq, child, free, shared] using run
  · have acquired := Record.FramedLogProperties.lock_poll
      ({pidCounter := 2, processes := [(2,{})], nativeResourceTypes := resourceTypes,
        schedule := [.swap 2]} : Environment) 7 decodedFrame false before
      (by decide) (by simp [Record.FramedLogProperties.Apart, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
      (by simp [decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    simpa [guard1, free, held1, shared, Record.FramedLogProperties.framedEnv,
      Record.FramedLogProperties.guard, Record.FramedLogProperties.held] using acquired
  · simpa [resume, resource, beforeCounter, guard1, held1, free,
      Record.ScheduledLogProperties.owner, Record.ScheduledLogProperties.frame,
      Record.ScheduledLogProperties.afterFrame, Rustler.encodeBool, recoverGuard] using parentTrace
  · simp [NativeMutex.pollLock, shared, overlappingFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells, held1, NativeMutex.lockedContents, NativeCodec.decode]
  · have acquired := Record.FramedLogProperties.lock_poll
      ({currentPid := 2, pidCounter := 2, nativeResourceTypes := resourceTypes} : Environment)
      9 afterFirstFrame false committed1
      (by decide) (by simp [Record.FramedLogProperties.Apart, afterFirstFrame, overlappingFrame,
        decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
      (by simp [afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    simpa [guard2, free, held2, shared, Record.FramedLogProperties.framedEnv,
      Record.FramedLogProperties.guard, Record.FramedLogProperties.held] using acquired
  · simpa [resume, resource, beforeCounter, guard2, held2, free,
      Record.ScheduledLogProperties.owner, Record.ScheduledLogProperties.frame,
      Record.ScheduledLogProperties.afterFrame, Rustler.encodeBool, recoverGuard] using childTrace

theorem contended_records :
    let parent := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 6) (.integer 13)
    let child := Elixir.LynxIoFixture.Native.«log_append/2» (Dispatcher.ofTable #[] 0) (.reference 6) (.integer 19)
    (Result.schedule child (fun _ => parent))
      {refCounter := 6, nativeHeap := (shared 6 pinnedFrame (Record.FramedLogProperties.free false) firstInput).2,
        schedule := [.current, .swap 2]} =
      (.ok Term.true, {
        pidCounter := 2, refCounter := 10, nativeResourceTypes := resourceTypes,
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


end Record.ContendedAdapterProperties
