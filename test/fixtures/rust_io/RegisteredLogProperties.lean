module
public import Record.ScheduledLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.RegisteredLogProperties
open NativeFile Record.Properties Record.CrashProperties Record.AppendProperties Record.RecoveryProperties
  Record.LockedProperties Record.SharedLogProperties Record.FramedLogProperties
  Record.NativeLogProperties Record.OverlappingLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeFile.typeName NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

@[expose] def shared (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (state : State) : Nat × List (Nat × String × Term) :=
  (counter, frame ++ [(2, NativeFile.typeName, encode state), (1, NativeMutex.typeName NativeFile, contents)])

private theorem framed_eq (env : Environment) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (state : State) (count : env.nativeRefCounter = counter)
    (heap : env.nativeHeap = (shared counter frame contents state).2) :
    framedEnv env counter frame contents state = env := by
  cases env
  simp_all [shared, framedEnv]

private theorem seek_ready (pid : PID) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State) (position : U64)
    (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Record.Properties.Valid before)
    (ready : blocked before = false)
    (step : seekStep before (.end_ 0#i64) = some (.Ok position, after))
    (env : Environment) (_owner : env.currentPid = pid)
    (count : env.nativeRefCounter = counter) (heap : env.nativeHeap = (shared counter frame contents before).2) :
    pollSeek ⟨2⟩ (.end_ 0#i64) env = some (.ok (.Ok position, ⟨2⟩),
      {env with nativeRefCounter := counter, nativeHeap := (shared counter frame contents after).2}) := by
  have found := seek_poll env counter frame contents before after position apart bound valid ready step
  rw [framed_eq env counter frame contents before count heap] at found
  exact found

private theorem write_ready (pid : PID) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State) (value : U16)
    (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Record.Properties.Valid before)
    (ready : blocked before = false)
    (step : writeStep before (payload value) = some (.Ok 4#usize, after))
    (env : Environment) (_owner : env.currentPid = pid)
    (count : env.nativeRefCounter = counter) (heap : env.nativeHeap = (shared counter frame contents before).2) :
    pollWrite ⟨2⟩ (payload value) env = some (.ok (.Ok 4#usize, ⟨2⟩),
      {env with nativeRefCounter := counter, nativeHeap := (shared counter frame contents after).2}) := by
  have found := write_poll env counter frame contents before after value apart bound valid ready step
  rw [framed_eq env counter frame contents before count heap] at found
  exact found

private theorem sync_ready (pid : PID) (counter : Nat) (frame : List (Nat × String × Term))
    (contents : Term) (before after : State)
    (apart : Apart 2 frame) (bound : 2 ≤ counter) (valid : Record.Properties.Valid before)
    (ready : blocked before = false) (step : syncStep before = some (.Ok (), after))
    (env : Environment) (_owner : env.currentPid = pid)
    (count : env.nativeRefCounter = counter) (heap : env.nativeHeap = (shared counter frame contents before).2) :
    pollSync ⟨2⟩ env = some (.ok (.Ok ()),
      {env with nativeRefCounter := counter, nativeHeap := (shared counter frame contents after).2}) := by
  have found := sync_poll env counter frame contents before after apart bound valid ready step
  rw [framed_eq env counter frame contents before count heap] at found
  exact found

@[expose] def counter (first : Bool) : Nat := if first then 7 else 9
@[expose] def frame (first : Bool) := if first then decodedFrame else afterFirstFrame
@[expose] def afterFrame (_first : Bool) := pinnedFrame
@[expose] def owner (first : Bool) : NativeResourceArc shared_log.LogResource := ⟨3, if first then 7 else 9⟩
@[expose] def count (_first : Bool) : Nat := 2

private theorem drop_steps (pid : PID) (first : Bool) (state : State) :
    Result.SharedSteps pid (do NativeOwnedDrop.drop (owner first); NativeM.ok true)
      (shared (counter first + 1) (frame first) (Record.FramedLogProperties.free false) state) true
      (shared (counter first + 1) (afterFrame first) (Record.FramedLogProperties.free false) state) := by
  have released := NativeResourceArc.releaseOwned_live_sharedSteps pid (owner first) logPayload (count first)
    (shared (counter first + 1) (frame first) (Record.FramedLogProperties.free false) state)
    (shared (counter first + 1) (afterFrame first) (Record.FramedLogProperties.free false) state)
    (fun _ => NativeM.ok true) true
    (by cases first <;> decide) (by cases first <;> decide)
    (by cases first <;> simp [owner, frame, shared, afterFirstFrame, overlappingFrame,
      decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by cases first <;> simp [owner, frame, count, shared, afterFirstFrame, overlappingFrame,
      decodedFrame, pinnedFrame, NativeResourceArc.vmCells])
    (by cases first <;> simp [owner, frame, count, shared, afterFirstFrame, overlappingFrame,
      decodedFrame, pinnedFrame, NativeResourceArc.vmCells]) ?_
  · simpa only [NativeOwnedDrop.drop] using released
  · cases first with
    | false =>
      simpa [NativeM.ok, owner, frame, afterFrame, count, counter, shared, afterFirstFrame, overlappingFrame,
        decodedFrame, pinnedFrame, NativeResourceArc.vmCells, List.filter] using
          (Result.SharedSteps.done (pid := pid) true
            (shared 10 pinnedFrame (Record.FramedLogProperties.free false) state))
    | true =>
      simpa [NativeM.ok, owner, frame, afterFrame, count, counter, shared, afterFirstFrame, overlappingFrame,
        decodedFrame, pinnedFrame, NativeResourceArc.vmCells, List.filter] using
          (Result.SharedSteps.done (pid := pid) true
            (shared 8 pinnedFrame (Record.FramedLogProperties.free false) state))

private theorem body_steps (pid : PID) (first : Bool)
    (before sought written committed : State) (value : U16) (position : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought)
    (valid2 : Record.Properties.Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    let guard : NativeGuard NativeFile := ⟨⟨1⟩, counter first + 1, pid, ⟨2⟩⟩
    Result.SharedSteps pid (afterGuard (owner first) guard value)
      (shared (counter first + 1) (frame first) (NativeMutex.lockedContents pid (counter first + 1) false
        (⟨2⟩ : NativeFile)) before) true
      (shared (counter first + 1) (afterFrame first) (Record.FramedLogProperties.free false) committed) := by
  dsimp only
  simp only [afterGuard, Record.RollbackProperties.append_contract, bind_assoc, NativeFile.seek,
    Result.wait_bind]
  have apart2 : Apart 2 (frame first) := by
    cases first <;> simp [Apart, frame, afterFirstFrame, overlappingFrame, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells]
  have bound : 2 ≤ counter first + 1 := by cases first <;> decide
  let locked := NativeMutex.lockedContents pid (counter first + 1) false (⟨2⟩ : NativeFile)
  refine .wait _ _ (.ok (.Ok position, (⟨2⟩ : NativeFile))) _
    (shared (counter first + 1) (frame first) locked sought) _ _
    (seek_ready pid (counter first + 1) (frame first) locked before sought position apart2 bound valid0 ready0 seek) ?_
  simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok 4#usize, (⟨2⟩ : NativeFile))) _
    (shared (counter first + 1) (frame first) locked written) _ _
    (write_ready pid (counter first + 1) (frame first) locked sought written value apart2 bound valid1 ready1 write) ?_
  simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (shared (counter first + 1) (frame first) locked committed) _ _
    (sync_ready pid (counter first + 1) (frame first) locked written committed apart2 bound valid2 ready2 sync) ?_
  simp only [Result.ok_bind, NativeGuard.release, Result.wait_bind]
  refine .wait _ _ (.ok ()) _
    (shared (counter first + 1) (frame first) (Record.FramedLogProperties.free false) committed) _ _ ?_ ?_
  · intro env actor refs cells
    have freed := release_framed env (counter first + 1) (counter first + 1) (frame first) false committed
      (by cases first <;> simp [Apart, frame, afterFirstFrame, overlappingFrame, decodedFrame,
        pinnedFrame, NativeResourceArc.vmCells])
    rw [actor] at freed
    rw [framed_eq env (counter first + 1) (frame first) locked committed refs cells] at freed
    simpa [shared, framedEnv] using freed
  · simpa only [Result.ok_bind] using drop_steps pid first committed

/-- A complete extracted native caller retains resource reads, mutex/file
waits and owner-release reads/writes as distinct scheduled steps. -/
theorem call_steps (pid : PID) (first : Bool)
    (before sought written committed : State) (value : U16) (position : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought)
    (valid2 : Record.Properties.Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.SharedSteps pid (__APPEND__ (owner first) value)
      (shared (counter first) (frame first) (Record.FramedLogProperties.free false) before) true
      (shared (counter first + 1) (afterFrame first) (Record.FramedLogProperties.free false) committed) := by
  rw [caller_contract]
  apply NativeResourceArc.deref_live_sharedSteps pid (owner first) logPayload (count first)
  · cases first <;> decide
  · cases first <;> decide
  · cases first <;> simp [owner, frame, shared, afterFirstFrame, overlappingFrame,
      decodedFrame, pinnedFrame, NativeResourceArc.vmCells]
  · cases first <;> simp [owner, frame, count, shared, afterFirstFrame, overlappingFrame,
      decodedFrame, pinnedFrame, NativeResourceArc.vmCells]
  · cases first <;> simp [owner, frame, count, shared, afterFirstFrame, overlappingFrame,
      decodedFrame, pinnedFrame, NativeResourceArc.vmCells]
  · simp only [logPayload, NativeMutex.lock, Result.wait_bind]
    refine .wait _ _ (.ok (.Ok (⟨⟨1⟩, counter first + 1, pid, ⟨2⟩⟩ : NativeGuard NativeFile))) _
      (shared (counter first + 1) (frame first)
        (NativeMutex.lockedContents pid (counter first + 1) false (⟨2⟩ : NativeFile)) before) _ _ ?_ ?_
    · intro env actor refs cells
      have acquired := lock_poll env (counter first) (frame first) false before
        (by cases first <;> decide)
        (by cases first <;> simp [Apart, frame, afterFirstFrame, overlappingFrame, decodedFrame,
          pinnedFrame, NativeResourceArc.vmCells])
        (by cases first <;> simp [frame, counter, afterFirstFrame, overlappingFrame, decodedFrame,
          pinnedFrame, NativeResourceArc.vmCells])
      rw [framed_eq env (counter first) (frame first) (Record.FramedLogProperties.free false) before refs cells]
        at acquired
      simpa [shared, framedEnv, Record.FramedLogProperties.guard, Record.FramedLogProperties.held, actor] using acquired
    · simpa [Result.ok_bind, recoverGuard] using body_steps pid first before sought written committed value position
        valid0 valid1 valid2 ready0 ready1 ready2 seek write sync


/-- Decoding starts from the VM pin, not a predecoded Rust owner. The token
allocated by that actual decoder is passed to the extracted facade. -/
theorem decoded_call_steps (pid : PID) (first : Bool) (types : List String)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ types)
    (before sought written committed : State) (value : U16) (position : U64)
    (valid0 : Record.Properties.Valid before) (valid1 : Record.Properties.Valid sought)
    (valid2 : Record.Properties.Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.RegisteredSteps pid (do
      let resource ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__APPEND__ resource value) Rustler.encodeBool)
      (shared (counter first - 1) pinnedFrame (Record.FramedLogProperties.free false) before)
      types Term.true
      (shared (counter first + 1) pinnedFrame (Record.FramedLogProperties.free false) committed) types := by
  apply NativeResourceArc.decode_live_registeredSteps pid (⟨3,5⟩ : NativeResourceArc shared_log.LogResource)
    6 logPayload 1 _ _ types types _ Term.true registered (by decide) (by decide)
  · simp [shared, pinnedFrame, NativeResourceArc.vmCells]
  · simp [shared, pinnedFrame, NativeResourceArc.vmCells]
  · simp [shared, pinnedFrame, NativeResourceArc.vmCells]
  · simp [shared, pinnedFrame, NativeResourceArc.vmCells]
  · cases first <;> simp [counter, shared, pinnedFrame, NativeResourceArc.vmCells]
  · have native := call_steps pid first before sought written committed value position
      valid0 valid1 valid2 ready0 ready1 ready2 seek write sync
    have encoded := Rustler.executeNative_sharedSteps native Rustler.encodeBool
    apply Result.RegisteredSteps.shared (types := types) at encoded
    cases first <;>
      simpa [shared, counter, frame, owner, afterFrame, afterFirstFrame, overlappingFrame,
        decodedFrame, pinnedFrame, NativeResourceArc.vmCells, Rustler.encodeBool] using encoded

end Record.RegisteredLogProperties
