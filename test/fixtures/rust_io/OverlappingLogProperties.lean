module
public import Record.NativeLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.OverlappingLogProperties
open NativeFile Record.Properties Record.CrashProperties Record.AppendProperties
  Record.LockedProperties Record.SharedLogProperties Record.FramedLogProperties
  Record.NativeLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeFile.typeName NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

/-- The continuation after the actual compiled caller acquires its guard. -/
@[expose] def afterGuard (resource : NativeResourceArc shared_log.LogResource)
    (guard : NativeGuard NativeFile) (value : U16) : NativeM Bool := do
  let (reply, file) ← append_record_or_rollback guard.value value
  NativeGuard.release {guard with value := file}
  NativeOwnedDrop.drop resource
  match reply with
  | .Ok accepted => NativeM.ok accepted
  | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false

/-- The continuation is linked to the extracted caller, rather than assumed
to implement its contract. -/
theorem caller_contract (resource : NativeResourceArc shared_log.LogResource) (value : U16) :
    __APPEND__ resource value = (do
      let log ← NativeResourceArc.deref resource
      let acquired ← NativeMutex.lock log.file
      afterGuard resource (recoverGuard acquired) value) := by
  rw [facade_contract, Record.SharedLogProperties.critical_contract]
  simp only [afterGuard, bind_assoc, NativeM.ok, Result.ok_bind]
  rfl

@[expose] def firstHeld (env : Environment) (state : State) : Environment :=
  framedEnv env 8 decodedFrame (held env 7 false) state

theorem acquired_prefix (env : Environment) (state : State) (value : U16) :
    Result.ReadyPrefix (__APPEND__ ⟨3,7⟩ value) (decoded env 7 state)
      (afterGuard ⟨3,7⟩ (guard env 7) value) (firstHeld env state) := by
  rw [caller_contract]
  have read := (NativeResourceArc.deref_live_prefix
    (⟨3,7⟩ : NativeResourceArc shared_log.LogResource) logPayload 2 (decoded env 7 state)
    (by decide) (by decide)
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [decoded, framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])).bind
      (fun log => do
        let acquired ← NativeMutex.lock log.file
        afterGuard ⟨3,7⟩ (recoverGuard acquired) value)
  apply read.trans
  simp only [Result.ok_bind, logPayload, NativeMutex.lock, Result.wait_bind]
  refine .wait _ _ _ _ _ _ _
    (lock_poll env 7 decodedFrame false state (by decide)
      (by simp [Apart, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
      (by simp [decodedFrame, pinnedFrame, NativeResourceArc.vmCells])) ?_
  simpa [Result.ok_bind, recoverGuard, firstHeld] using
    (Result.ReadyPrefix.refl (afterGuard ⟨3,7⟩ (guard env 7) value) (firstHeld env state))

@[expose] def overlappingFrame : List (Nat × String × Term) :=
  (9, NativeResourceArc.handleType shared_log.LogResource, .nativeReference 3) ::
    decodedFrame.map fun cell => if cell.1 == 3 then
      (3, NativeResourceArc.typeName shared_log.LogResource,
        .tuple #[.integer 3, NativeCodec.encode logPayload]) else cell

@[expose] def overlapping (env : Environment) (peer : PID) (state : State) : Environment :=
  framedEnv {env with currentPid := peer} 9 overlappingFrame (held env 7 false) state

/-- A second actual decoder acquires an owner while the first file guard is
still held. It changes resource metadata and the global counter, not the guard. -/
theorem decode_while_held (env : Environment) (peer : PID) (state : State)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6))
      (framedEnv {env with currentPid := peer} 8 decodedFrame (held env 7 false) state)
      (.ok (⟨3,9⟩ : NativeResourceArc shared_log.LogResource)) (overlapping env peer state) := by
  have trace := NativeResourceArc.decode_live_prefix
    (⟨3,5⟩ : NativeResourceArc shared_log.LogResource) 6 logPayload 2
    (framedEnv {env with currentPid := peer} 8 decodedFrame (held env 7 false) state)
    registered (by decide) (by decide)
    (by simp [framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
  simpa [overlapping, framedEnv, overlappingFrame] using trace

/-- The other caller cannot acquire while the original guard owns this mutex. -/
theorem peer_blocked (env : Environment) (peer : PID) (state : State)
    (different : peer ≠ env.currentPid) :
    NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile) (overlapping env peer state) = none := by
  simp [NativeMutex.pollLock, overlapping, framedEnv, overlappingFrame, decodedFrame,
    pinnedFrame, NativeResourceArc.vmCells, Record.FramedLogProperties.held, NativeMutex.lockedContents,
    NativeCodec.decode, Ne.symm different]

/-- Resuming the first guard after the other decoder allocated token 9 still
releases token 8, preserves the new owner and leaves the counter at 9. -/
theorem release_after_decode (env : Environment) (state : State) :
    NativeGuard.pollRelease (guard env 7) (overlapping env env.currentPid state) =
      some (.ok (), framedEnv env 9 overlappingFrame (Record.FramedLogProperties.free false) state) := by
  exact release_framed env 9 8 overlappingFrame false state
    (by simp [Apart, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])

@[expose] def afterFirstFrame : List (Nat × String × Term) :=
  (overlappingFrame.filter fun cell => cell.1 != 7).map fun cell => if cell.1 == 3 then
    (3, NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 2, NativeCodec.encode logPayload]) else cell

@[expose] def firstDone (env : Environment) (state : State) : Environment :=
  framedEnv env 9 afterFirstFrame (Record.FramedLogProperties.free false) state

/-- The first caller consumes only owner 7. The other Rust owner and VM pin
remain live, so no payload destructor or file close is run. -/
theorem release_first (env : Environment) (state : State) :
    Result.ReadyPrefix (NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource))
      (framedEnv env 9 overlappingFrame (Record.FramedLogProperties.free false) state)
      (.ok ()) (firstDone env state) := by
  have trace := NativeResourceArc.releaseOwned_live_prefix
    (⟨3,7⟩ : NativeResourceArc shared_log.LogResource) logPayload 3
    (framedEnv env 9 overlappingFrame (Record.FramedLogProperties.free false) state)
    (by decide) (by decide)
    (by simp [framedEnv, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
  simpa [NativeOwnedDrop.drop, firstDone, framedEnv, afterFirstFrame, List.filter_append, List.map_append, List.filter] using trace

/-- Resume the actual first caller's continuation after the second decoder.
Every file poll uses the updated heap/counter while the original guard token
and resource ownership are retained until their respective releases. -/
theorem finish_first (env : Environment) (before sought written committed : State)
    (value : U16) (position : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought)
    (valid2 : Record.Properties.Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.ReadyPrefix (afterGuard ⟨3,7⟩ (guard env 7) value)
      (overlapping env env.currentPid before) (.ok true) (firstDone env committed) := by
  have guarded := guarded_prefix env 9 8 overlappingFrame false before sought written committed value position
    (by decide)
    (by simp [Apart, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [Apart, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    valid0 valid1 valid2 ready0 ready1 ready2 seek write sync
  have body := guarded.bind (fun reply => do
    NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource)
    match reply with
    | .Ok accepted => NativeM.ok accepted
    | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false)
  have front : Result.ReadyPrefix (afterGuard ⟨3,7⟩ (guard env 7) value)
      (overlapping env env.currentPid before)
      (do NativeOwnedDrop.drop (⟨3,7⟩ : NativeResourceArc shared_log.LogResource); NativeM.ok true)
      (framedEnv env 9 overlappingFrame (Record.FramedLogProperties.free false) committed) := by
    simpa [afterGuard, Record.FramedLogProperties.guard, overlapping, Record.FramedLogProperties.held, NativeM.ok, bind_assoc] using body
  apply front.trans
  simpa [NativeM.ok] using (release_first env committed).bind (fun _ => NativeM.ok true)

@[expose] def done (env : Environment) (state : State) : Environment :=
  framedEnv env 10 pinnedFrame (Record.FramedLogProperties.free false) state

/-- The remaining actual Rustler caller can append and consume owner 9 after
the first caller has released. Its guard uses token 10, not an older token. -/
theorem second_call (env : Environment) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.ReadyPrefix (__APPEND__ ⟨3,9⟩ value) (firstDone env (appendInput data position rest))
      (.ok true) (done env (appended (appendInput data position rest) value rest)) := by
  have borrowed := borrow_prefix (⟨3,9⟩ : NativeResourceArc shared_log.LogResource) logPayload value 2
    (firstDone env (appendInput data position rest)) (by decide) (by decide)
    (by simp [firstDone, framedEnv, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells])
    (by simp [firstDone, framedEnv, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells])
    (by simp [firstDone, framedEnv, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells])
  have critical := (Record.FramedLogProperties.append_success env 9 afterFirstFrame false data value position rest
    (by decide)
    (by simp [Apart, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [Apart, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    fits offset).1
  have body := borrowed.trans critical
  rw [facade_contract]
  have front := body.bind (fun reply => do
    NativeOwnedDrop.drop (⟨3,9⟩ : NativeResourceArc shared_log.LogResource)
    match reply with
    | .Ok accepted => NativeM.ok accepted
    | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false)
  have released := NativeResourceArc.releaseOwned_live_prefix
    (⟨3,9⟩ : NativeResourceArc shared_log.LogResource) logPayload 2
    (framedEnv env 10 afterFirstFrame (Record.FramedLogProperties.free false)
      (appended (appendInput data position rest) value rest))
    (by decide) (by decide)
    (by simp [framedEnv, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by simp [framedEnv, afterFirstFrame, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
  have tail := released.bind (fun _ => NativeM.ok true)
  apply front.trans
  simpa [NativeOwnedDrop.drop, NativeM.ok, done, firstDone, framedEnv, afterFirstFrame,
    overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells, List.filter] using tail

/-- Implementation-linked phases for a decoder arriving inside the first
critical section. These explicit prefixes do not assume that a scheduler has
already composed the callers or proved progress. -/
theorem overlap_phases (env : Environment) (peer : PID)
    (before sought written committed : State) (value : U16) (position : U64)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ env.nativeResourceTypes)
    (different : peer ≠ env.currentPid)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought)
    (valid2 : Record.Properties.Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.ReadyPrefix (__APPEND__ ⟨3,7⟩ value) (decoded env 7 before)
      (afterGuard ⟨3,7⟩ (guard env 7) value) (firstHeld env before) ∧
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 6))
      (framedEnv {env with currentPid := peer} 8 decodedFrame (held env 7 false) before)
      (.ok (⟨3,9⟩ : NativeResourceArc shared_log.LogResource)) (overlapping env peer before) ∧
    NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile) (overlapping env peer before) = none ∧
    Result.ReadyPrefix (afterGuard ⟨3,7⟩ (guard env 7) value)
      (overlapping env env.currentPid before) (.ok true) (firstDone env committed) := by
  exact ⟨acquired_prefix env before value, decode_while_held env peer before registered,
    peer_blocked env peer before different,
    finish_first env before sought written committed value position valid0 valid1 valid2
      ready0 ready1 ready2 seek write sync⟩

end Record.OverlappingLogProperties
