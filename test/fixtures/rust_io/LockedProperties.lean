module
public import Record.MalformedProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.LockedProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties

/-- Guard payloads contain only the file identity; file bytes stay in their
independent heap cell and cannot be restored from an acquisition snapshot. -/
theorem file_codec (file : NativeFile) :
    NativeCodec.encode file = .reference file.id ∧ NativeCodec.decode (α := NativeFile) (.reference file.id) = some file := by
  cases file
  simp [NativeCodec.encode, NativeCodec.decode]

@[expose] def recoverGuard :
    core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)) → NativeGuard NativeFile
  | .Ok guard => guard
  | .Err error => NativePoisonError.into_inner error

/-- The actual critical section retains its guard through the complete append
and releases the reconstructed file identity afterward, including IO errors. -/
theorem critical_contract (mutex : NativeMutex NativeFile) (value : U16) :
    locked_append mutex value = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recoverGuard acquired
      let (reply, file) ← append_record guard.value value
      NativeGuard.release {guard with value := file}
      NativeM.ok reply) := by
  simp only [locked_append, monadLift_self, NativeM.lift, NativeM.ok, Result.ok_bind,
    NativeGuard.deref_mut, NativeDrop.drop]
  apply congrArg (fun next => NativeMutex.lock mutex >>= next)
  funext acquired
  cases acquired <;> simp [recoverGuard]

/-- The actual append computation uses the actual Rust encoder before writing,
with decoding of IO results and error propagation retained. -/
theorem append_contract (file : NativeFile) (value : U16) :
    append_record file value = (do
      let (position, file) ← NativeFile.seek file (.end_ 0#i64)
      match position with
      | .Err error => NativeM.ok (.Err error, file)
      | .Ok _ =>
        let (written, file) ← NativeFile.write file (payload value)
        match written with
        | .Err error => NativeM.ok (.Err error, file)
        | .Ok amount =>
          let synced ← NativeFile.syncAll file
          match synced with
          | .Err error => NativeM.ok (.Err error, file)
          | .Ok () => NativeM.ok (.Ok (amount = 4#usize), file)) := by
  simp only [append_record, io_core.seek_from, Record.Extraction.FileModel.seek,
    write_record, encode_spec, write_then_sync, io_core.write_once, io_core.synchronize,
    NativeM.ok, monadLift_self, Array.to_slice, NativeM.lift, Result.ok_bind, bind_assoc]
  apply congrArg (fun next => NativeFile.seek file (.end_ 0#i64) >>= next)
  funext found
  rcases found with ⟨seek, file⟩
  cases seek with
  | Err error => rfl
  | Ok position =>
    apply congrArg (fun next => NativeFile.write file (payload value) >>= next)
    funext found
    rcases found with ⟨written, file⟩
    cases written with
    | Err error => rfl
    | Ok amount =>
      simp only [bind_assoc]
      apply congrArg (fun next => NativeFile.syncAll file >>= next)
      funext synced
      cases synced with
      | Err error => rfl
      | Ok returned =>
        cases returned
        by_cases same : amount.val = 4
        · have equal : amount = 4#usize := by scalar_tac
          simp [equal]
        · have unequal : amount ≠ 4#usize := by intro equal; simp [equal] at same
          simp [unequal]

/-- Compose the actual seek/write/sync with an arbitrary caller continuation.
The poll equations specify executable model transitions, not assumed Rust contracts. -/
theorem append_next (file : NativeFile) (value : U16) (s0 s1 s2 s3 : Environment) (position : U64)
    (seek : pollSeek file (.end_ 0#i64) s0 = some (.ok (.Ok position, file), s1))
    (write : pollWrite file (payload value) s1 = some (.ok (.Ok 4#usize, file), s2))
    (sync : pollSync file s2 = some (.ok (.Ok ()), s3))
    (next : core.result.Result Bool NativeIoError × NativeFile → NativeM α) :
    (append_record file value >>= next) s0 = next (.Ok true, file) s3 := by
  rw [append_contract]
  simp only [bind_assoc, NativeFile.seek, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ seek]
  simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ write]
  simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ sync]
  simp [NativeM.ok]

/-- A different native execution context cannot acquire the file mutex while
this guard is held. This states safety at the boundary, not fairness or liveness. -/
theorem contention_waits (mutex : NativeMutex NativeFile) (file : NativeFile)
    (value : U16) (owner token : Nat) (poisoned : Bool) (env : Environment)
    (different : owner ≠ env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id, NativeMutex.typeName NativeFile, NativeMutex.lockedContents owner token poisoned file)]) :
    locked_append mutex value = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recoverGuard acquired
      let (reply, file) ← append_record guard.value value
      NativeGuard.release {guard with value := file}
      NativeM.ok reply) ∧ NativeMutex.pollLock mutex env = none := by
  refine ⟨critical_contract mutex value, ?_⟩
  cases poisoned <;> simp [NativeMutex.pollLock, NativeMutex.lockedContents, stored, different]

/-- Execute a complete actual critical section through acquisition, file IO
and release. Every premise is a concrete executable poll equation. -/
theorem critical_steps (mutex : NativeMutex NativeFile) (value : U16) (guard : NativeGuard NativeFile)
    (s0 s1 s2 s3 s4 s5 : Environment) (position : U64)
    (acquired : core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)))
    (lock : NativeMutex.pollLock mutex s0 = some (.ok acquired, s1))
    (recovered : recoverGuard acquired = guard)
    (seek : pollSeek guard.value (.end_ 0#i64) s1 = some (.ok (.Ok position, guard.value), s2))
    (write : pollWrite guard.value (payload value) s2 = some (.ok (.Ok 4#usize, guard.value), s3))
    (sync : pollSync guard.value s3 = some (.ok (.Ok ()), s4))
    (release : NativeGuard.pollRelease guard s4 = some (.ok (), s5)) :
    locked_append mutex value s0 = (.ok (.Ok true), s5) := by
  rw [critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ lock]
  simp only [Result.ok_bind, recovered]
  rw [append_next guard.value value s1 s2 s3 s4 position seek write sync]
  simp only [NativeGuard.release, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ release]
  simp [NativeM.ok]

@[expose] def unlocked (base : Environment) (state : State) (poisoned : Bool) (counter : Nat) : Environment :=
  fileEnv {base with refCounter := counter} ⟨2⟩ state
    [(1, NativeMutex.typeName NativeFile, .tuple #[.atom "unlocked",
      .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode (⟨2⟩ : NativeFile)])]

@[expose] def held (base : Environment) (state : State) (poisoned : Bool) : Environment :=
  fileEnv {base with refCounter := 3} ⟨2⟩ state
    [(1, NativeMutex.typeName NativeFile, NativeMutex.lockedContents base.currentPid 3 poisoned (⟨2⟩ : NativeFile))]

@[expose] def guard (base : Environment) : NativeGuard NativeFile := ⟨⟨1⟩, 3, base.currentPid, ⟨2⟩⟩

theorem held_lookup (base : Environment) (state : State) (poisoned : Bool) (valid : Valid state) :
    lookup (⟨2⟩ : NativeFile) (held base state poisoned) = some state := by
  exact lookup_at {base with refCounter := 3} ⟨2⟩ state
    [(1, NativeMutex.typeName NativeFile, NativeMutex.lockedContents base.currentPid 3 poisoned (⟨2⟩ : NativeFile))]
    (by simp [Separate]) valid

theorem held_store (base : Environment) (before after : State) (poisoned : Bool) :
    store (⟨2⟩ : NativeFile) after (held base before poisoned) = held base after poisoned := by
  exact store_at {base with refCounter := 3} ⟨2⟩ before after
    [(1, NativeMutex.typeName NativeFile, NativeMutex.lockedContents base.currentPid 3 poisoned (⟨2⟩ : NativeFile))]
    (by simp [Separate])

/-- Actual lock acquisition and release frame the independent file cell. File
writes made inside the critical section survive the subsequent guard release. -/
theorem locked_ready (base : Environment) (before sought written committed : State) (value : U16)
    (position : U64) (poisoned : Bool)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok 4#usize, written))
    (sync : syncStep written = some (.Ok (), committed)) :
    locked_append ⟨1⟩ value (unlocked base before poisoned 2) =
      (.ok (.Ok true), unlocked base committed poisoned 3) := by
  have lock := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex NativeFile) (⟨2⟩ : NativeFile)
    poisoned (unlocked base before poisoned 2)
    (by simp [unlocked, fileEnv]) (by simp [unlocked, fileEnv])
  have lockReady : NativeMutex.pollLock (⟨1⟩ : NativeMutex NativeFile) (unlocked base before poisoned 2) =
      some (.ok (if poisoned then .Err ⟨guard base⟩ else .Ok (guard base)), held base before poisoned) := by
    simpa [unlocked, held, guard, fileEnv] using lock
  have seekReady : pollSeek (⟨2⟩ : NativeFile) (.end_ 0#i64) (held base before poisoned) =
      some (.ok (.Ok position, ⟨2⟩), held base sought poisoned) := by
    simp only [pollSeek]
    rw [held_lookup base before poisoned valid0]
    simp [ready0, seek, held_store]
  have writeReady : pollWrite (⟨2⟩ : NativeFile) (payload value) (held base sought poisoned) =
      some (.ok (.Ok 4#usize, ⟨2⟩), held base written poisoned) := by
    simp only [pollWrite]
    rw [held_lookup base sought poisoned valid1]
    simp [ready1, write, held_store]
  have syncReady : pollSync (⟨2⟩ : NativeFile) (held base written poisoned) =
      some (.ok (.Ok ()), held base committed poisoned) := by
    simp only [pollSync]
    rw [held_lookup base written poisoned valid2]
    simp [ready2, sync, held_store]
  have releaseReady : NativeGuard.pollRelease (guard base) (held base committed poisoned) =
      some (.ok (), unlocked base committed poisoned 3) := by
    cases poisoned <;> simp [NativeGuard.pollRelease, guard, held, unlocked, fileEnv,
      NativeMutex.lockedContents, NativeCodec.encode, NativeCodec.decode]
  exact critical_steps _ value (guard base) _ _ _ _ _ _ position _ lockReady
    (by cases poisoned <;> rfl) seekReady writeReady syncReady releaseReady

@[expose] def appendInput (data : ByteArray) (position : Nat) (rest : Term) : State :=
  ⟨data, data, position, outcome "seek" true 0 (zeroMask data)
    (outcome "write" true 4 (zeroMask data) (outcome "sync_all" true 0 ByteArray.empty rest))⟩

/-- The actual locked Rust append preserves every earlier byte, acknowledges
only a synchronized record, and unlocks without restoring pre-write file data. -/
theorem locked_success (base : Environment) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (poisoned : Bool)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    locked_append ⟨1⟩ value (unlocked base (appendInput data position rest) poisoned 2) =
      (.ok (.Ok true), unlocked base (appended (appendInput data position rest) value rest) poisoned 3) ∧
    (appended (appendInput data position rest) value rest).visible.data.toList =
      data.data.toList ++ (encoded value).data.toList := by
  let before := appendInput data position rest
  let afterSeek := sought before data.size data
    (outcome "write" true 4 (zeroMask data) (outcome "sync_all" true 0 ByteArray.empty rest))
  let afterWrite := written afterSeek (payload value) 4 data (outcome "sync_all" true 0 ByteArray.empty rest)
  have bound : data.size ≤ limit := by omega
  have valid0 : Valid before := ⟨bound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨bound, Nat.le_refl _, bound⟩
  have accepted : persist afterSeek.durable
      (overwrite afterSeek.visible afterSeek.position (bytes (payload value)) 4) (zeroMask data) = some data := by
    exact persist_keep_old _ _
  have valid2 := written_valid afterSeek (payload value) 4 (zeroMask data) data (outcome "sync_all" true 0 ByteArray.empty rest) valid1
    (by simp [payload, layout]) (by exact fits) accepted
  refine ⟨locked_ready base before afterSeek afterWrite (appended before value rest) value
    (U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)) poisoned valid0 valid1 valid2
    (by simp [before, appendInput, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome])
    (by simp [afterWrite, written, blocked, outcome]) ?_ ?_ ?_, append_bytes data value⟩
  · simpa only [afterSeek, before, appendInput] using seek_end_step before valid0 (zeroMask data) data _
      (action_outcome _ _ _ _ _) (persist_zero data)
  · simpa [afterWrite, count, Usize.ofNatCore, UScalar.ofNat] using write_step afterSeek (payload value) 4 (zeroMask data) data _
      (by simp [payload, layout]) (by simp [payload, layout, limit]) fits
      (action_outcome _ _ _ _ _) accepted
  · simp [syncStep, afterWrite, written, afterSeek, sought, before, appendInput,
      appended, action_outcome]

/-- A write error still reaches guard release and is returned as an error;
there is no synchronization or successful append acknowledgement on this path. -/
theorem critical_error_steps (mutex : NativeMutex NativeFile) (value : U16) (guard : NativeGuard NativeFile)
    (s0 s1 s2 s3 s4 : Environment) (position : U64) (error : NativeIoError)
    (acquired : core.result.Result (NativeGuard NativeFile) (NativePoisonError (NativeGuard NativeFile)))
    (lock : NativeMutex.pollLock mutex s0 = some (.ok acquired, s1))
    (recovered : recoverGuard acquired = guard)
    (seek : pollSeek guard.value (.end_ 0#i64) s1 = some (.ok (.Ok position, guard.value), s2))
    (write : pollWrite guard.value (payload value) s2 = some (.ok (.Err error, guard.value), s3))
    (release : NativeGuard.pollRelease guard s3 = some (.ok (), s4)) :
    locked_append mutex value s0 = (.ok (.Err error), s4) := by
  rw [critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ lock]
  simp only [Result.ok_bind, recovered]
  rw [append_contract]
  simp only [bind_assoc, NativeFile.seek, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ seek]
  simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ write]
  simp only [NativeM.ok, Result.ok_bind, NativeGuard.release, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ release]
  simp

end Record.LockedProperties
