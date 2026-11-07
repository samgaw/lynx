module
public import Record.LockedConcurrent
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RollbackProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.LockedProperties Record.LockedConcurrent

private theorem terminal_bind (value : α) (next : α → Lynx.Result β) :
    Lynx.Result.bind (Lynx.Result.ok value) next = next value := rfl

/-- The actual Rust computation distinguishes a complete write from a short
write and invokes the actual first-party resize/sync caller on the latter. -/
theorem append_contract (file : NativeFile) (value : U16) :
    append_record_or_rollback file value = (do
      let (position, file) ← NativeFile.seek file (.end_ 0#i64)
      match position with
      | .Err error => NativeM.ok (.Err error, file)
      | .Ok start =>
        let (written, file) ← NativeFile.write file (payload value)
        match written with
        | .Err error => NativeM.ok (.Err error, file)
        | .Ok amount =>
          match amount.val with
          | 4 =>
            let synced ← NativeFile.syncAll file
            match synced with
            | .Err error => NativeM.ok (.Err error, file)
            | .Ok () => NativeM.ok (.Ok true, file)
          | _ =>
            let resized ← resize_then_sync file start
            match resized with
            | .Err error => NativeM.ok (.Err error, file)
            | .Ok () => NativeM.ok (.Ok false, file)) := by
  simp only [append_record_or_rollback, io_core.seek_from, Record.Extraction.FileModel.seek,
    encode_spec, io_core.write_once, io_core.synchronize, monadLift_self,
    NativeM.lift, NativeM.ok, Result.ok_bind, Array.to_slice]
  apply congrArg (fun next => NativeFile.seek file (.end_ 0#i64) >>= next)
  funext found
  rcases found with ⟨seek, file⟩
  cases seek with
  | Err error => rfl
  | Ok start =>
    apply congrArg (fun next => NativeFile.write file (payload value) >>= next)
    funext found
    rcases found with ⟨written, file⟩
    cases written with
    | Err error => rfl
    | Ok amount =>
      dsimp only
      by_cases complete : amount.val = 4
      · simp only [complete]
        apply congrArg (fun next => NativeFile.syncAll file >>= next)
        funext reply
        cases reply with
        | Err error => rfl
        | Ok returned => cases returned; rfl
      · simp only
        apply congrArg (fun next => resize_then_sync file start >>= next)
        funext reply
        cases reply with
        | Err error => rfl
        | Ok returned => cases returned; rfl

theorem critical_contract (mutex : NativeMutex NativeFile) (value : U16) :
    locked_append_or_rollback mutex value = (do
      let acquired ← NativeMutex.lock mutex
      let guard := recoverGuard acquired
      let (reply, file) ← append_record_or_rollback guard.value value
      NativeGuard.release {guard with value := file}
      NativeM.ok reply) := by
  simp only [locked_append_or_rollback, monadLift_self, NativeM.lift, NativeM.ok, Result.ok_bind,
    NativeGuard.deref_mut, NativeDrop.drop]
  apply congrArg (fun next => NativeMutex.lock mutex >>= next)
  funext acquired
  cases acquired <;> simp [recoverGuard]

@[expose] def postAcquire (value : U16)
    (reply : Except Exception (core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile)))) : Result Term :=
  match reply with
  | .error error => .error error
  | .ok acquired => do
      let guard := recoverGuard acquired
      let (reply, file) ← append_record_or_rollback guard.value value
      NativeGuard.release {guard with value := file}
      finish reply

theorem worker_wait (value : U16) :
    (do let reply ← locked_append_or_rollback ⟨1⟩ value
        finish reply : Result Term) = .wait (NativeMutex.pollLock ⟨1⟩) (postAcquire value) := by
  rw [critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind, bind_assoc]
  congr 1
  funext reply
  cases reply <;> simp [postAcquire, NativeM.ok]

@[expose] def afterWrite (guard : NativeGuard NativeFile) (start : U64) (amount : Usize) : Result Term :=
  (match amount.val with
    | 4 => NativeFile.syncAll guard.value >>= fun synced =>
      match synced with
      | .Err error => NativeM.ok (.Err error, guard.value)
      | .Ok () => NativeM.ok (.Ok true, guard.value)
    | _ => resize_then_sync guard.value start >>= fun resized =>
      match resized with
      | .Err error => NativeM.ok (.Err error, guard.value)
      | .Ok () => NativeM.ok (.Ok false, guard.value))
    >>= fun pair => NativeGuard.release {guard with value := pair.2} >>= fun _ => finish pair.1

private theorem prefix_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (before sought written : State) (value : U16) (position : U64) (amount : Usize)
    (result : Term) (final : Nat × List (Nat × String × Term)) (fresh : 2 ≤ counter)
    (valid0 : Valid before) (valid1 : Valid sought)
    (ready0 : blocked before = false) (ready1 : blocked sought = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok amount, written))
    (suffix : Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position amount)
      (shared counter (owned pid token) written) result final) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) before) result final := by
  simp only [postAcquire, recoverGuard]
  rw [append_contract]
  simp only [bind_assoc, NativeFile.seek, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok position, (⟨2⟩ : NativeFile))) _
    (shared counter (owned pid token) sought) _ _ ?_ ?_ ?_
  · intro env _ count heap
    exact seek_poll before sought position counter _ valid0 ready0 seek fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter before different env owner heap
  · simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
    refine .wait _ _ (.ok (.Ok amount, (⟨2⟩ : NativeFile))) _
      (shared counter (owned pid token) written) _ _ ?_ ?_ ?_
    · intro env _ count heap
      exact write_result_poll sought written value (.Ok amount) counter _ valid1 ready1 write fresh env count heap
    · intro env owner _ heap
      exact held_blocked pid peer token counter sought different env owner heap
    · simp only [Result.ok_bind]
      exact suffix

private theorem release_trace (pid peer token counter : Nat) (state : State) (reply : Term)
    (different : pid ≠ peer) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (NativeGuard.release (⟨⟨1⟩, token, pid, ⟨2⟩⟩ : NativeGuard NativeFile) >>= fun _ => .ok reply)
      (shared counter (owned pid token) state) reply (shared counter free state) := by
  simp only [NativeGuard.release, Result.wait_bind]
  refine .wait _ _ (.ok ()) _ (shared counter free state) _ _ ?_ ?_ ?_
  · intro env owner count heap
    simp [NativeGuard.pollRelease, heap, shared, owned, free,
      NativeMutex.lockedContents, NativeCodec.encode, NativeCodec.decode, owner, count]
  · intro env owner _ heap
    exact held_blocked pid peer token counter state different env owner heap
  · exact .done reply _

theorem set_len_poll (before after : State) (length : U64) (counter : Nat) (contents : Term)
    (valid : Valid before) (ready : blocked before = false)
    (step : setLenStep before length = some (.Ok (), after)) (fresh : 2 ≤ counter)
    (env : Environment) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter contents before).2) :
    pollSetLen (⟨2⟩ : NativeFile) length env =
      some (.ok (.Ok ()),
        {env with refCounter := counter, nativeHeap := (shared counter contents after).2}) := by
  have found : lookup (⟨2⟩ : NativeFile) env = some before := by
    simp [lookup, heap, shared, decode_encode before valid]
    omega
  simp only [pollSetLen, found]
  simp [ready, step, store, heap, shared, ← count]

private theorem complete_suffix (pid peer token counter : Nat) (different : pid ≠ peer)
    (written committed : State) (position : U64) (fresh : 2 ≤ counter)
    (valid : Valid written) (ready : blocked written = false)
    (sync : syncStep written = some (.Ok (), committed)) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position 4#usize)
      (shared counter (owned pid token) written) Term.true (shared counter free committed) := by
  simp only [afterWrite, NativeFile.syncAll, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (shared counter (owned pid token) committed) _ _ ?_ ?_ ?_
  · intro env _ count heap
    exact sync_poll written committed counter _ valid ready sync fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter written different env owner heap
  · simpa [NativeM.ok, finish, bind_assoc, terminal_bind] using release_trace pid peer token counter committed Term.true different

private theorem short_suffix (pid peer token counter : Nat) (different : pid ≠ peer)
    (written resized committed : State) (position : U64) (amount : Usize)
    (short : amount.val ≠ 4) (fresh : 2 ≤ counter)
    (valid0 : Valid written) (valid1 : Valid resized)
    (ready0 : blocked written = false) (ready1 : blocked resized = false)
    (truncate : setLenStep written position = some (.Ok (), resized))
    (sync : syncStep resized = some (.Ok (), committed)) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position amount)
      (shared counter (owned pid token) written) Term.false (shared counter free committed) := by
  simp only [afterWrite]
  simp only [resize_then_sync, io_core.resize_to, io_core.synchronize, monadLift_self,
    bind_assoc, NativeFile.setLen, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (shared counter (owned pid token) resized) _ _ ?_ ?_ ?_
  · intro env _ count heap
    exact set_len_poll written resized position counter _ valid0 ready0 truncate fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter written different env owner heap
  · simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
    refine .wait _ _ (.ok (.Ok ())) _ (shared counter (owned pid token) committed) _ _ ?_ ?_ ?_
    · intro env _ count heap
      exact sync_poll resized committed counter _ valid1 ready1 sync fresh env count heap
    · intro env owner _ heap
      exact held_blocked pid peer token counter resized different env owner heap
    · simpa [NativeM.ok, finish, bind_assoc, terminal_bind] using release_trace pid peer token counter committed Term.false different

theorem truncate_append (data bytes : ByteArray) (amount : Nat) :
    resize (overwrite data data.size bytes amount) data.size = data := by
  apply ByteArray.ext
  by_cases zero : amount = 0
  · simp [overwrite, zero, resize, ← ByteArray.size_data, ← Array.length_toList]
  · simp [overwrite, zero, resize, ← ByteArray.size_data, ← Array.length_toList]


private theorem success_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (fresh : 2 ≤ counter) (data : ByteArray) (value : U16) (position : Nat) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (appendInput data position rest)) Term.true
      (shared counter free (appended (appendInput data position rest) value rest)) := by
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
  have valid2 := written_valid afterSeek (payload value) 4 (zeroMask data) data
    (outcome "sync_all" true 0 ByteArray.empty rest) valid1
    (by simp [payload, layout]) fits accepted
  refine prefix_trace pid peer token counter different before afterSeek afterWrite value
    (U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)) 4#usize _ _ fresh valid0 valid1
    (by simp [before, appendInput, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, appendInput] using seek_end_step before valid0 (zeroMask data) data _
      (action_outcome _ _ _ _ _) (persist_zero data)
  · simpa [afterWrite, count, Usize.ofNatCore, UScalar.ofNat] using write_step afterSeek (payload value) 4 (zeroMask data) data _
      (by simp [payload, layout]) (by simp [payload, layout, limit]) fits
      (action_outcome _ _ _ _ _) accepted
  · apply complete_suffix pid peer token counter different afterWrite (appended before value rest) _ fresh valid2
      (by simp [afterWrite, written, blocked, outcome])
    simp [syncStep, afterWrite, written, afterSeek, sought, before, appendInput,
      appended, action_outcome]

@[expose] def rollbackInput (data : ByteArray) (position amount : Nat) (rest : Term) : State :=
  ⟨data, data, position, outcome "seek" true 0 (zeroMask data)
    (outcome "write" true amount (zeroMask data)
      (outcome "set_len" true 0 (zeroMask data)
        (outcome "sync_all" true 0 ByteArray.empty
          (appendInput data (data.size + amount) rest).script)))⟩

private theorem rollback_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (fresh : 2 ≤ counter) (data : ByteArray) (value : U16) (position amount : Nat) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) (short : amount < 4) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (rollbackInput data position amount rest)) Term.false
      (shared counter free (appendInput data (data.size + amount) rest)) := by
  let next := appendInput data (data.size + amount) rest
  let syncRest := outcome "sync_all" true 0 ByteArray.empty next.script
  let resizeRest := outcome "set_len" true 0 (zeroMask data) syncRest
  let before := rollbackInput data position amount rest
  let afterSeek := sought before data.size data (outcome "write" true amount (zeroMask data) resizeRest)
  let afterWrite := written afterSeek (payload value) amount data resizeRest
  let afterResize : State := ⟨data, data, data.size + amount, syncRest⟩
  have bound : data.size ≤ limit := by omega
  have positionBound : data.size + amount ≤ limit := by omega
  have bounded : amount ≤ (payload value).val.length := by simp [payload, layout]; omega
  have valid0 : Valid before := ⟨bound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨bound, Nat.le_refl _, bound⟩
  have accepted : persist afterSeek.durable
      (overwrite afterSeek.visible afterSeek.position (bytes (payload value)) amount) (zeroMask data) = some data := by
    exact persist_keep_old _ _
  have valid2 := written_valid afterSeek (payload value) amount (zeroMask data) data resizeRest valid1
    bounded positionBound accepted
  have valid3 : Valid afterResize := ⟨bound, Nat.le_refl _, positionBound⟩
  let size := U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)
  let amountValue := count (payload value) amount bounded
  refine prefix_trace pid peer token counter different before afterSeek afterWrite value size amountValue _ _ fresh
    valid0 valid1 (by simp [before, rollbackInput, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, rollbackInput, resizeRest, syncRest, next, size] using
      seek_end_step before valid0 (zeroMask data) data _ (action_outcome _ _ _ _ _) (persist_zero data)
  · exact write_step afterSeek (payload value) amount (zeroMask data) data resizeRest
      bounded (by simp [payload, layout, limit]) positionBound (action_outcome _ _ _ _ _) accepted
  · refine short_suffix pid peer token counter different afterWrite afterResize next size amountValue
      (by simp only [amountValue, count, Usize.ofNatCore, UScalar.ofNatCore_val_eq]; omega)
      fresh valid2 valid3
      (by simp [afterWrite, written, resizeRest, blocked, outcome])
      (by simp [afterResize, syncRest, blocked, outcome]) ?_ ?_
    · simp [setLenStep, size, U64.ofNatCore, afterWrite, written, afterSeek, sought,
        resizeRest, action_outcome, before, rollbackInput, truncate_append, afterResize, syncRest, next,
        not_lt.mpr bound, persist_zero]
    · simp [syncStep, afterResize, syncRest, next, appendInput, action_outcome]

private theorem full_success_trace (pid : Nat) (data : ByteArray) (value : U16)
    (position : Nat) (rest : Term) (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) :
    Result.SharedSteps pid (.wait (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire value))
      (shared 3 free (appendInput data position rest)) Term.true
      (shared 4 free (appended (appendInput data position rest) value rest)) := by
  refine .wait _ _ (.ok (.Ok (⟨⟨1⟩, 4, pid, ⟨2⟩⟩ : NativeGuard NativeFile))) _
    (shared 4 (owned pid 4) (appendInput data position rest)) _ _ ?_
    (success_trace pid (pid + 1) 4 4 (by omega) (by decide) data value position rest fits offset).ready
  intro env owner count heap
  exact lock_poll pid 3 _ (by decide) env owner count heap

/-- A short first write is durably rolled back before another caller can
append. Every finite schedule preserves the original prefix and only the
successful caller's complete record, even with a retained beyond-EOF offset. -/
theorem rollback_then_append_all_schedules (data : ByteArray) (first second : U16)
    (position amount : Nat) (rest : Term) (fits : data.size + 4 ≤ limit)
    (offset : position ≤ limit) (short : amount < 4) (choices : List ScheduleChoice) :
    let before := rollbackInput data position amount rest
    let next := appendInput data (data.size + amount) rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do
      let _ ← Result.schedule (worker second) .ok
      worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.ok Term.false, shared 4 free (appended next second rest)) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.ok Term.true, shared 4 free (appended next first rest)) := by
  dsimp only
  let before := rollbackInput data position amount rest
  let next := appendInput data (data.size + amount) rest
  have bounded : data.size + amount ≤ limit := by omega
  have rootTrace := rollback_trace 1 2 3 3 (by decide) (by decide) data first position amount rest fits offset short
  have childTrace := rollback_trace 2 1 3 3 (by decide) (by decide) data second position amount rest fits offset short
  have childAfter := full_success_trace 2 data second (data.size + amount) rest fits bounded
  have rootAfter := full_success_trace 1 data first (data.size + amount) rest fits bounded
  have result := Result.two_wait_serial_orders
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨2⟩⟩))
    Term.false Term.false Term.true Term.true
    (shared 2 free before) (shared 3 (owned 1 3) before) (shared 3 free next)
    (shared 4 free (appended next second rest))
    (shared 3 (owned 2 3) before) (shared 3 free next)
    (shared 4 free (appended next first rest))
    (lock_poll 1 2 before (by decide)) (lock_poll 2 2 before (by decide))
    rootTrace childAfter childTrace rootAfter choices
  simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared, before, next] using result

private theorem unit_poll (before after : State) (counter : Nat) (contents : Term)
    (step : State → Option (core.result.Result Unit NativeIoError × State))
    (poll : NativeFile → Environment → Option (Except Exception (core.result.Result Unit NativeIoError) × Environment))
    (equation : ∀ file env, poll file env = (
      match lookup file env with
      | none => some (.error .exhausted, env)
      | some state => if blocked state then none else
        match step state with
        | none => some (.error .exhausted, env)
        | some (reply, updated) => some (.ok reply, store file updated env)))
    (reply : core.result.Result Unit NativeIoError)
    (valid : Admitted before) (ready : blocked before = false)
    (transition : step before = some (reply, after)) (fresh : 2 ≤ counter)
    (env : Environment) (count : env.refCounter = counter)
    (heap : env.nativeHeap = (shared counter contents before).2) :
    poll ⟨2⟩ env = some (.ok reply,
      {env with refCounter := counter, nativeHeap := (shared counter contents after).2}) := by
  have found : lookup (⟨2⟩ : NativeFile) env = some before := by
    simp [lookup, heap, shared, decode_admitted before valid]
    omega
  rw [equation]
  simp [found, ready, transition, store, heap, shared, ← count]

private theorem truncate_error_suffix (pid peer token counter : Nat) (different : pid ≠ peer)
    (written failed : State) (position : U64) (amount : Usize) (error : NativeIoError)
    (short : amount.val ≠ 4) (fresh : 2 ≤ counter) (valid : Admitted written)
    (ready : blocked written = false)
    (truncate : setLenStep written position = some (.Err error, failed)) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position amount)
      (shared counter (owned pid token) written) (errorTerm error.identity)
      (shared counter free failed) := by
  simp only [afterWrite]
  simp only [resize_then_sync, io_core.resize_to, monadLift_self, bind_assoc,
    NativeFile.setLen, Result.wait_bind]
  refine .wait _ _ (.ok (.Err error)) _ (shared counter (owned pid token) failed) _ _ ?_ ?_ ?_
  · intro env _ count heap
    exact unit_poll written failed counter _ (fun state => setLenStep state position)
      (fun file => pollSetLen file position) (by intros; rfl) (.Err error)
      valid ready truncate fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter written different env owner heap
  · simpa [NativeM.ok, finish, bind_assoc, terminal_bind] using
      release_trace pid peer token counter failed (errorTerm error.identity) different

private theorem sync_error_suffix (pid peer token counter : Nat) (different : pid ≠ peer)
    (written resized failed : State) (position : U64) (amount : Usize) (error : NativeIoError)
    (short : amount.val ≠ 4) (fresh : 2 ≤ counter)
    (valid0 : Admitted written) (valid1 : Admitted resized)
    (ready0 : blocked written = false) (ready1 : blocked resized = false)
    (truncate : setLenStep written position = some (.Ok (), resized))
    (sync : syncStep resized = some (.Err error, failed)) :
    Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position amount)
      (shared counter (owned pid token) written) (errorTerm error.identity)
      (shared counter free failed) := by
  simp only [afterWrite]
  simp only [resize_then_sync, io_core.resize_to, io_core.synchronize, monadLift_self,
    bind_assoc, NativeFile.setLen, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (shared counter (owned pid token) resized) _ _ ?_ ?_ ?_
  · intro env _ count heap
    exact unit_poll written resized counter _ (fun state => setLenStep state position)
      (fun file => pollSetLen file position) (by intros; rfl) (.Ok ())
      valid0 ready0 truncate fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter written different env owner heap
  · simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
    refine .wait _ _ (.ok (.Err error)) _ (shared counter (owned pid token) failed) _ _ ?_ ?_ ?_
    · intro env _ count heap
      exact unit_poll resized failed counter _ syncStep pollSync (by intros; rfl)
        (.Err error) valid1 ready1 sync fresh env count heap
    · intro env owner _ heap
      exact held_blocked pid peer token counter resized different env owner heap
    · simpa [NativeM.ok, finish, bind_assoc, terminal_bind] using
        release_trace pid peer token counter failed (errorTerm error.identity) different

private theorem acquire_trace (pid peer counter : Nat)
    (before after : State) (value : U16) (reply : Term) (fresh : 2 ≤ counter)
    (trace : Result.ExclusiveSteps pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, counter + 1, pid, ⟨2⟩⟩)))
      (shared (counter + 1) (owned pid (counter + 1)) before) reply
      (shared (counter + 1) free after)) :
    Result.SharedSteps pid (do
      let result ← locked_append_or_rollback ⟨1⟩ value
      finish result : Result Term)
      (shared counter free before) reply (shared (counter + 1) free after) := by
  rw [worker_wait]
  refine .wait _ _ (.ok (.Ok ⟨⟨1⟩, counter + 1, pid, ⟨2⟩⟩)) _
    (shared (counter + 1) (owned pid (counter + 1)) before) _ _ ?_ trace.ready
  intro env owner count heap
  exact lock_poll pid counter before fresh env owner count heap

/-- Failed truncation propagates its error and releases the actual changed file
state. All background persistence admitted by the executable transition is retained. -/
theorem rollback_resize_failure (pid counter : Nat) (before sought written failed : State)
    (value : U16) (position : U64) (amount : Usize) (error : NativeIoError)
    (short : amount.val ≠ 4) (fresh : 2 ≤ counter)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Admitted written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false)
    (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok amount, written))
    (truncate : setLenStep written position = some (.Err error, failed)) :
    Result.SharedSteps pid (do
      let result ← locked_append_or_rollback ⟨1⟩ value
      finish result : Result Term)
      (shared counter free before) (errorTerm error.identity) (shared (counter + 1) free failed) := by
  apply acquire_trace pid (pid + 1) counter before failed value _ fresh
  exact prefix_trace pid (pid + 1) (counter + 1) (counter + 1) (by omega)
    before sought written value position amount _ _ (by omega) valid0 valid1 ready0 ready1 seek write
    (truncate_error_suffix pid (pid + 1) (counter + 1) (counter + 1) (by omega)
      written failed position amount error short (by omega) valid2 ready2 truncate)

/-- A failed sync after successful truncation preserves the truncated visible
length, potentially longer durable image, cursor and error through guard release. -/
theorem rollback_sync_failure (pid counter : Nat) (before sought written resized failed : State)
    (value : U16) (position : U64) (amount : Usize) (error : NativeIoError)
    (short : amount.val ≠ 4) (fresh : 2 ≤ counter)
    (valid0 : Valid before) (valid1 : Valid sought)
    (valid2 : Admitted written) (valid3 : Admitted resized)
    (ready0 : blocked before = false) (ready1 : blocked sought = false)
    (ready2 : blocked written = false) (ready3 : blocked resized = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok amount, written))
    (truncate : setLenStep written position = some (.Ok (), resized))
    (sync : syncStep resized = some (.Err error, failed)) :
    Result.SharedSteps pid (do
      let result ← locked_append_or_rollback ⟨1⟩ value
      finish result : Result Term)
      (shared counter free before) (errorTerm error.identity) (shared (counter + 1) free failed) := by
  apply acquire_trace pid (pid + 1) counter before failed value _ fresh
  exact prefix_trace pid (pid + 1) (counter + 1) (counter + 1) (by omega)
    before sought written value position amount _ _ (by omega) valid0 valid1 ready0 ready1 seek write
    (sync_error_suffix pid (pid + 1) (counter + 1) (counter + 1) (by omega)
      written resized failed position amount error short (by omega) valid2 valid3 ready2 ready3 truncate sync)

/-- A real short-write trace witnesses both error paths without assumed poll
results. The short tail persists before the attempted rollback. -/
@[expose] def rollbackErrorStart (syncFailure : Bool) (errorId : Nat) (rest : Term) : State :=
  let tail : ByteArray := ⟨#[1, 0]⟩
  let sync := outcome "sync_all" false errorId (zeroMask tail) rest
  let rollback := if syncFailure then outcome "set_len" true 0 (zeroMask tail) sync
    else outcome "set_len" false errorId (zeroMask tail) rest
  ⟨ByteArray.empty, ByteArray.empty, 0, outcome "seek" true 0 ByteArray.empty
    (outcome "write" true 2 ⟨#[1, 1]⟩ rollback)⟩

@[expose] def rollbackErrorEnd (syncFailure : Bool) (rest : Term) : State :=
  ⟨if syncFailure then ByteArray.empty else ⟨#[1, 0]⟩, ⟨#[1, 0]⟩, 2, rest⟩

/-- Both actual Rust error paths retain the durable short tail and release the
mutex. On sync failure the visible file is empty but durable bytes remain. -/
theorem rollback_failure_effects (syncFailure : Bool) (errorId : Nat) (rest : Term) :
    let before := rollbackErrorStart syncFailure errorId rest
    let after := rollbackErrorEnd syncFailure rest
    let observed := (do
      let result ← locked_append_or_rollback ⟨1⟩ 1#u16
      finish result : Result Term)
      {currentPid := 1, refCounter := 2, nativeHeap := (shared 2 free before).2}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
      (.ok (errorTerm errorId), shared 3 free after) := by
  let tail : ByteArray := ⟨#[1, 0]⟩
  let before := rollbackErrorStart syncFailure errorId rest
  let seeked := {before with position := 0, script := (
    outcome "write" true 2 ⟨#[1, 1]⟩
      (if syncFailure then outcome "set_len" true 0 (zeroMask tail)
        (outcome "sync_all" false errorId (zeroMask tail) rest)
      else outcome "set_len" false errorId (zeroMask tail) rest))}
  let written : State := ⟨tail, tail, 2,
    if syncFailure then outcome "set_len" true 0 (zeroMask tail)
      (outcome "sync_all" false errorId (zeroMask tail) rest)
    else outcome "set_len" false errorId (zeroMask tail) rest⟩
  let resized : State := ⟨ByteArray.empty, tail, 2,
    outcome "sync_all" false errorId (zeroMask tail) rest⟩
  have seek : seekStep before (.end_ 0#i64) = some (.Ok 0#u64, seeked) := by
    simp [before, rollbackErrorStart, seeked, seekStep, seekTarget, action_outcome, tail,
      zeroMask, persist, ← ByteArray.size_data]
    constructor
    · scalar_tac
    · rfl
  have payloadBytes : bytes (payload 1#u16) = (⟨#[1, 0, 254, 255]⟩ : ByteArray) := by
    have inverse : (~~~(1#u16)) = 65534#u16 := by
      simp
      rfl
    rw [payload_bytes]
    simp only [encoded, inverse]
    simp [fourBytes, rawByte, low, high]
    decide
  have write : writeStep seeked (payload 1#u16) = some (.Ok 2#usize, written) := by
    simp only [writeStep, payloadBytes]
    simp [seeked, before, rollbackErrorStart, action_outcome, written, tail,
      payload, layout, overwrite, persist, limit, ← ByteArray.size_data]
    rfl
  have initial : Valid before := by simp [before, rollbackErrorStart, Valid, limit]
  have soughtValid : Valid seeked := by simp [seeked, before, rollbackErrorStart, Valid, limit]
  have writtenValid : Admitted written := by simp [written, tail, Admitted, limit, ← ByteArray.size_data]
  have ready0 : blocked before = false := by simp [before, rollbackErrorStart, blocked, outcome]
  have ready1 : blocked seeked = false := by simp [seeked, blocked, outcome]
  have ready2 : blocked written = false := by cases syncFailure <;> simp [written, blocked, outcome]
  have trace : Result.SharedSteps 1 (do
      let result ← locked_append_or_rollback ⟨1⟩ 1#u16
      finish result : Result Term)
      (shared 2 free before) (errorTerm errorId)
      (shared 3 free (rollbackErrorEnd syncFailure rest)) := by
    cases selected : syncFailure with
    | false =>
      apply rollback_resize_failure 1 2 before seeked written (rollbackErrorEnd false rest)
        1#u16 0#u64 2#usize ⟨errorId⟩ (by decide) (by decide)
        initial soughtValid writtenValid ready0 ready1 ready2 seek write
      simp [written, selected, rollbackErrorEnd, setLenStep, action_outcome, tail, zeroMask,
        persist, limit, ← ByteArray.size_data]
      decide
    | true =>
      apply rollback_sync_failure 1 2 before seeked written resized (rollbackErrorEnd true rest)
        1#u16 0#u64 2#usize ⟨errorId⟩ (by decide) (by decide)
        initial soughtValid writtenValid (by simp [resized, tail, Admitted, limit, ← ByteArray.size_data])
        ready0 ready1 ready2 (by simp [resized, blocked, outcome]) seek write
      · simp [written, selected, resized, setLenStep, action_outcome, tail, zeroMask,
          resize, persist, limit, ← ByteArray.size_data]
        decide
      · simp [resized, rollbackErrorEnd, syncStep, action_outcome, tail, zeroMask,
          persist, ← ByteArray.size_data]
        decide
  let env : Environment := {currentPid := 1, refCounter := 2, nativeHeap := (shared 2 free before).2}
  have ran := trace.apply env rfl rfl rfl
  dsimp only
  rw [ran]

end Record.RollbackProperties
