module
public import Record.ConstructedLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConstructedConcurrentProperties
open NativeFile Record.Properties Record.CrashProperties Record.LockedProperties
  Record.OverlappingLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType
  NativeFile.writableHandleTypeName NativeFile.inodeTypeName NativeFile.namespaceTypeName NativeFile.closedDirectoryTypeName

inductive Phase where
  | pinned | decoded | overlapping | remaining

@[expose] def payload : shared_log.LogResource := Record.ConstructorLogProperties.payload
@[expose] def pinnedFrame := NativeResourceArc.vmCells payload 5 7 8
@[expose] def decodedFrame :=
  (9, NativeResourceArc.handleType shared_log.LogResource, .reference 5) ::
    pinnedFrame.map fun cell => if cell.1 == 5 then
      (5, NativeResourceArc.typeName shared_log.LogResource, .tuple #[.integer 2, NativeCodec.encode payload]) else cell
@[expose] def overlappingFrame :=
  (11, NativeResourceArc.handleType shared_log.LogResource, .reference 5) ::
    decodedFrame.map fun cell => if cell.1 == 5 then
      (5, NativeResourceArc.typeName shared_log.LogResource, .tuple #[.integer 3, NativeCodec.encode payload]) else cell
@[expose] def remainingFrame :=
  (overlappingFrame.filter fun cell => cell.1 != 9).map fun cell => if cell.1 == 5 then
    (5, NativeResourceArc.typeName shared_log.LogResource, .tuple #[.integer 2, NativeCodec.encode payload]) else cell
@[expose] def frame : Phase → List (Nat × String × Term)
  | .pinned => pinnedFrame
  | .decoded => decodedFrame
  | .overlapping => overlappingFrame
  | .remaining => remainingFrame
@[expose] def free : Term := Record.ConstructedLogProperties.free
@[expose] def shared (counter : Nat) (phase : Phase) (mutex : Term) (state : State) : Nat × List (Nat × String × Term) :=
  (counter, frame phase ++ [
    (4, NativeMutex.typeName NativeFile, mutex),
    (3, closedDirectoryTypeName, .tuple #[.nil]),
    (2, writableHandleTypeName, encodeHandle ⟨1,state.position,state.script⟩),
    (1, inodeTypeName, encode {state with position := 0,script := .nil}),
    (0, namespaceTypeName, encodeNamespace ⟨Record.ConstructorLogProperties.names,
      Record.ConstructorLogProperties.names,[],.nil⟩)])
@[expose] def world (env : Environment) (counter : Nat) (phase : Phase) (mutex : Term) (state : State) : Environment :=
  {env with refCounter := counter, nativeHeap := (shared counter phase mutex state).2}

private theorem world_eq (env : Environment) (counter : Nat) (phase : Phase)
    (mutex : Term) (state : State) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter phase mutex state).2) :
    world env counter phase mutex state = env := by
  cases env
  simp_all [world]

/-- Logical file state is reconstructed from the actual inode and writable
capability; it is not stored in a substitute standalone file cell. -/
theorem file_lookup (env : Environment) (counter : Nat) (phase : Phase) (mutex : Term) (state : State)
    (bound : 2 ≤ counter) (valid : Valid state) :
    NativeFile.lookup ⟨2⟩ (world env counter phase mutex state) = some state := by
  have node : NativeFile.decode (encode {state with position := 0,script := .nil}) =
      some {state with position := 0,script := .nil} :=
    Record.Properties.decode_encode _ ⟨valid.1,valid.2.1,Nat.zero_le _⟩
  have pos : ¬ limit < state.position := not_lt.mpr valid.2.2
  have positive : ¬ (state.position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  have one : ¬ counter < 1 := by omega
  have two : ¬ counter ≤ 1 := by omega
  cases phase <;>
    simp [NativeFile.lookup,world,shared,frame,pinnedFrame,decodedFrame,overlappingFrame,remainingFrame,NativeResourceArc.vmCells,sharedLookup,getHandle,decodeHandle,
      inode,encodeHandle,node,typeName,writableHandleTypeName,handleTypeName,pos,positive,bound,one,two]

/-- Writing through the constructor's capability updates the shared inode and
its cursor/script, preserving resource ownership, mutex and namespace cells. -/
theorem file_store (env : Environment) (counter : Nat) (phase : Phase) (mutex : Term) (before after : State)
    (valid : Valid before) :
    store ⟨2⟩ after (world env counter phase mutex before) = world env counter phase mutex after := by
  have pos : ¬ limit < before.position := not_lt.mpr valid.2.2
  have positive : ¬ (before.position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  cases phase <;>
    simp [store,world,shared,frame,pinnedFrame,decodedFrame,overlappingFrame,remainingFrame,NativeResourceArc.vmCells,decodeHandle,encodeHandle,sharedStore,
      typeName,writableHandleTypeName,handleTypeName,pos,positive]

theorem seek_poll (env : Environment) (counter : Nat) (phase : Phase) (mutex : Term) (before after : State) (position : U64)
    (bound : 2 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : seekStep before (.end_ 0#i64) = some (.Ok position,after)) :
    pollSeek ⟨2⟩ (.end_ 0#i64) (world env counter phase mutex before) =
      some (.ok (.Ok position,⟨2⟩),world env counter phase mutex after) := by
  unfold pollSeek
  rw [file_lookup env counter phase mutex before bound valid]
  simp only [ready,Bool.false_eq_true,↓reduceIte,step]
  rw [file_store env counter phase mutex before after valid]

theorem write_poll (env : Environment) (counter : Nat) (phase : Phase) (mutex : Term) (before after : State) (value : U16)
    (bound : 2 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : writeStep before (Record.CrashProperties.payload value) = some (.Ok 4#usize,after)) :
    pollWrite ⟨2⟩ (Record.CrashProperties.payload value) (world env counter phase mutex before) =
      some (.ok (.Ok 4#usize,⟨2⟩),world env counter phase mutex after) := by
  unfold pollWrite
  rw [file_lookup env counter phase mutex before bound valid]
  simp only [ready,Bool.false_eq_true,↓reduceIte,step]
  simp only [show getHandle (⟨2⟩ : NativeFile) handleTypeName (world env counter phase mutex before) = none by
    cases phase <;> simp [getHandle,world,shared,frame,pinnedFrame,decodedFrame,overlappingFrame,remainingFrame,NativeResourceArc.vmCells,handleTypeName,writableHandleTypeName]]
  congr 2
  exact file_store env counter phase mutex before after valid

theorem sync_poll (env : Environment) (counter : Nat) (phase : Phase) (mutex : Term) (before after : State)
    (bound : 2 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (),after)) :
    pollSync ⟨2⟩ (world env counter phase mutex before) = some (.ok (.Ok ()),world env counter phase mutex after) := by
  unfold pollSync
  rw [file_lookup env counter phase mutex before bound valid]
  simp only [ready,Bool.false_eq_true,↓reduceIte,step]
  rw [file_store env counter phase mutex before after valid]


/-- The actual constructor's output is the starting shared state, including its
closed directory, writable capability and synchronized namespace. -/
theorem constructed_shape (env : Environment) (script : Term) :
    Record.ConstructorLogProperties.constructed env script =
      world env 8 .pinned free ⟨ByteArray.empty,ByteArray.empty,0,script⟩ := by
  simp [Record.ConstructorLogProperties.constructed,Record.ConstructorLogProperties.mutexReady,
    Record.ConstructorLogProperties.directory,Record.ConstructorLogProperties.fileCells,
    world,shared,frame,pinnedFrame,payload,free,Record.ConstructedLogProperties.free]


theorem lock_poll (env : Environment) (refs : Nat) (phase : Phase) (state : State)
    (fresh : (shared refs phase free state).2.any (fun cell => cell.1 == refs + 1) = false) :
    NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile) (world env refs phase free state) =
      some (.ok (.Ok (⟨⟨4⟩,refs + 1,env.currentPid,⟨2⟩⟩ : NativeGuard NativeFile)),
        world env (refs + 1) phase (NativeMutex.lockedContents env.currentPid (refs + 1) false (⟨2⟩ : NativeFile)) state) := by
  have trace := NativeMutex.pollLock_unlocked (⟨4⟩ : NativeMutex NativeFile)
    (⟨2⟩ : NativeFile) false (world env refs phase free state)
    (by cases phase <;> simp [world,shared,frame,pinnedFrame,decodedFrame,overlappingFrame,
      remainingFrame,NativeResourceArc.vmCells,free,Record.ConstructedLogProperties.free]) fresh
  cases phase <;> simpa [world,shared,frame,pinnedFrame,decodedFrame,overlappingFrame,remainingFrame,
    NativeResourceArc.vmCells] using trace

theorem release_poll (env : Environment) (refs guardToken : Nat) (phase : Phase) (state : State) :
    NativeGuard.pollRelease (⟨⟨4⟩,guardToken,env.currentPid,⟨2⟩⟩ : NativeGuard NativeFile)
      (world env refs phase (NativeMutex.lockedContents env.currentPid guardToken false (⟨2⟩ : NativeFile)) state) =
      some (.ok (),world env refs phase free state) := by
  cases phase <;>
    simp [NativeGuard.pollRelease,world,shared,frame,pinnedFrame,decodedFrame,overlappingFrame,
      remainingFrame,NativeResourceArc.vmCells,NativeMutex.lockedContents,NativeCodec.decode,
      free,Record.ConstructedLogProperties.free]

@[expose] def bodyPhase (first : Bool) : Phase := if first then .overlapping else .remaining
@[expose] def afterPhase (first : Bool) : Phase := if first then .remaining else .pinned
@[expose] def owner (first : Bool) : NativeResourceArc shared_log.LogResource := ⟨5,if first then 9 else 11⟩
@[expose] def ownerCount (first : Bool) : Nat := if first then 3 else 2

private theorem drop_steps (pid : PID) (first : Bool) (refs : Nat) (state : State) :
    Result.SharedSteps pid (do NativeOwnedDrop.drop (owner first); NativeM.ok true)
      (shared refs (bodyPhase first) free state) true
      (shared refs (afterPhase first) free state) := by
  have released := NativeResourceArc.releaseOwned_live_sharedSteps pid (owner first) payload (ownerCount first)
    (shared refs (bodyPhase first) free state) (shared refs (afterPhase first) free state)
    (fun _ => NativeM.ok true) true
    (by cases first <;> decide) (by cases first <;> decide)
    (by cases first <;> simp [owner,bodyPhase,shared,frame,remainingFrame,overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells])
    (by cases first <;> simp [owner,bodyPhase,ownerCount,shared,frame,remainingFrame,overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells])
    (by cases first <;> simp [owner,bodyPhase,ownerCount,shared,frame,remainingFrame,overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells]) ?_
  · simpa only [NativeOwnedDrop.drop] using released
  · cases first with
    | false =>
      simpa [NativeM.ok,owner,bodyPhase,afterPhase,ownerCount,shared,frame,remainingFrame,
        overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,List.filter] using
          (Result.SharedSteps.done (pid := pid) true (shared refs .pinned free state))
    | true =>
      simpa [NativeM.ok,owner,bodyPhase,afterPhase,ownerCount,shared,frame,remainingFrame,
        overlappingFrame,decodedFrame,pinnedFrame,NativeResourceArc.vmCells,List.filter] using
          (Result.SharedSteps.done (pid := pid) true (shared refs .remaining free state))

/-- Both complete critical sections operate on the constructor's actual shared
inode. Another decoded owner and all namespace cells remain framed. -/
theorem body_steps (pid : PID) (first : Bool) (refs guardToken : Nat) (bound : 2 ≤ refs)
    (before sought written committed : State) (value : U16) (position : U64)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position,sought))
    (write : writeStep sought (Record.CrashProperties.payload value) = some (.Ok 4#usize,written))
    (sync : syncStep written = some (.Ok (),committed)) :
    let guard : NativeGuard NativeFile := ⟨⟨4⟩,guardToken,pid,⟨2⟩⟩
    Result.SharedSteps pid (afterGuard (owner first) guard value)
      (shared refs (bodyPhase first) (NativeMutex.lockedContents pid guardToken false (⟨2⟩ : NativeFile)) before) true
      (shared refs (afterPhase first) free committed) := by
  dsimp only
  let locked := NativeMutex.lockedContents pid guardToken false (⟨2⟩ : NativeFile)
  simp only [afterGuard,Record.RollbackProperties.append_contract,bind_assoc,NativeFile.seek,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok position,(⟨2⟩ : NativeFile))) _
    (shared refs (bodyPhase first) locked sought) _ _ ?_ ?_
  · intro env actor count heap
    have polled := seek_poll env refs (bodyPhase first) locked before sought position bound valid0 ready0 seek
    rw [world_eq env refs (bodyPhase first) locked before count heap] at polled
    exact polled
  simp only [Result.ok_bind,NativeFile.write,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok (4#usize : Usize),(⟨2⟩ : NativeFile))) _
    (shared refs (bodyPhase first) locked written) _ _ ?_ ?_
  · intro env actor count heap
    have polled := write_poll env refs (bodyPhase first) locked sought written value bound valid1 ready1 write
    rw [world_eq env refs (bodyPhase first) locked sought count heap] at polled
    exact polled
  simp only [Result.ok_bind,NativeFile.syncAll,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (shared refs (bodyPhase first) locked committed) _ _ ?_ ?_
  · intro env actor count heap
    have polled := sync_poll env refs (bodyPhase first) locked written committed bound valid2 ready2 sync
    rw [world_eq env refs (bodyPhase first) locked written count heap] at polled
    exact polled
  simp only [Result.ok_bind,NativeGuard.release,Result.wait_bind]
  refine .wait _ _ (.ok ()) _ (shared refs (bodyPhase first) free committed) _ _ ?_ ?_
  · intro env actor count heap
    have polled := release_poll env refs guardToken (bodyPhase first) committed
    rw [actor] at polled
    rw [world_eq env refs (bodyPhase first) locked committed count heap] at polled
    exact polled
  · simpa only [Result.ok_bind] using drop_steps pid first refs committed

@[expose] def beforeCounter (first : Bool) : Nat := if first then 8 else 10
@[expose] def beforeFrame (first : Bool) := if first then Phase.pinned else Phase.decoded
@[expose] def decodedOwners (first : Bool) := if first then Phase.decoded else Phase.overlapping
@[expose] def beforeCount (first : Bool) : Nat := if first then 1 else 2
@[expose] def resource (first : Bool) : NativeResourceArc shared_log.LogResource :=
  ⟨5, beforeCounter first + 1⟩

/-- The real continuation at the lock wait, including the native exception and
result adapter. The poll itself has not executed. -/
@[expose] def resume (first : Bool) (value : U16) :
    Except Exception (core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile))) → Result Term := fun reply =>
  Rustler.executeNative (do
    let acquired ← Result.ofExcept reply
    afterGuard (resource first) (recoverGuard acquired) value) Rustler.encodeBool

theorem resume_wait (first : Bool) (value : U16) :
    Rustler.executeNative (do
      let acquired ← NativeMutex.lock (⟨4⟩ : NativeMutex NativeFile)
      afterGuard (resource first) (recoverGuard acquired) value) Rustler.encodeBool =
      .wait (NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile)) (resume first value) := by
  rw [NativeMutex.lock, Result.wait_bind, Rustler.executeNative_wait]
  congr 1
  funext reply
  cases reply <;> rfl

/-- Actual resource decode and borrow end at the mutex wait. In the peer case,
that decoder runs while the other owner's guard is still held. -/
theorem decoded_lock_prefix (pid : PID) (first : Bool) (types : List String)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ types)
    (contents : Term) (state : State) (value : U16) :
    Result.RegisteredPrefix pid (do
      let owner ← NativeResourceArc.decode (.reference 8)
      Rustler.executeNative (__APPEND__ owner value) Rustler.encodeBool)
      (shared (beforeCounter first) (beforeFrame first) contents state) types
      (.wait (NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile)) (resume first value))
      (shared (beforeCounter first + 1) (decodedOwners first) contents state) types := by
  have decoded := NativeResourceArc.decode_live_registeredPrefix pid
    (⟨5,7⟩ : NativeResourceArc shared_log.LogResource) 8 payload (beforeCount first)
    (shared (beforeCounter first) (beforeFrame first) contents state) types
    registered
    (by cases first <;> decide) (by cases first <;> decide)
    (by cases first <;> simp [shared, beforeFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells, frame])
    (by cases first <;> simp [shared, beforeFrame, decodedFrame, pinnedFrame,
      NativeResourceArc.vmCells, frame])
    (by cases first <;> simp [shared, beforeFrame, beforeCount, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells, frame])
    (by cases first <;> simp [shared, beforeFrame, beforeCount, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells, frame])
    (by cases first <;> simp [shared, beforeFrame, beforeCounter, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells, frame])
  have borrowed := NativeResourceArc.deref_live_registeredPrefix pid (resource first) payload
    (beforeCount first + 1)
    (shared (beforeCounter first + 1) (decodedOwners first) contents state) types
    (by cases first <;> decide) (by cases first <;> decide)
    (by cases first <;> simp [shared, resource, beforeCounter, decodedOwners,
      overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells, frame])
    (by cases first <;> simp [shared, resource, beforeCounter, decodedOwners,
      beforeCount, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells, frame])
    (by cases first <;> simp [shared, resource, beforeCounter, decodedOwners,
      beforeCount, overlappingFrame, decodedFrame, pinnedFrame, NativeResourceArc.vmCells, frame])
  have native : Result.RegisteredPrefix pid (__APPEND__ (resource first) value)
      (shared (beforeCounter first + 1) (decodedOwners first) contents state) types
      (do let acquired ← NativeMutex.lock (⟨4⟩ : NativeMutex NativeFile)
          afterGuard (resource first) (recoverGuard acquired) value)
      (shared (beforeCounter first + 1) (decodedOwners first) contents state) types := by
    rw [caller_contract]
    simpa only [Result.ok_bind, payload, Record.ConstructorLogProperties.payload] using borrowed.bind
      (fun log => do let acquired ← NativeMutex.lock log.file
                     afterGuard (resource first) (recoverGuard acquired) value)
  have encoded := Rustler.executeNative_registeredPrefix native Rustler.encodeBool
  rw [resume_wait] at encoded
  have head := decoded.bind (fun owner => Rustler.executeNative (__APPEND__ owner value) Rustler.encodeBool)
  cases first <;>
    simp only [beforeCounter, beforeFrame, decodedOwners, beforeCount, Bool.false_eq_true,
      ↓reduceIte, Result.ok_bind] at head encoded ⊢
  all_goals
    apply head.trans
    simpa [resource, beforeCounter, shared, overlappingFrame, decodedFrame,
      pinnedFrame, NativeResourceArc.vmCells, frame, payload] using encoded


end Record.ConstructedConcurrentProperties
