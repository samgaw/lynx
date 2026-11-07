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

private def postAcquire (value : U16)
    (reply : Except Exception (core.result.Result (NativeGuard NativeFile)
      (NativePoisonError (NativeGuard NativeFile)))) : Result Term :=
  match reply with
  | .error error => .error error
  | .ok acquired => do
      let guard := recoverGuard acquired
      let (reply, file) ← append_record_or_rollback guard.value value
      NativeGuard.release {guard with value := file}
      finish reply

private theorem worker_wait (value : U16) :
    (do let reply ← locked_append_or_rollback ⟨1⟩ value
        finish reply : Result Term) = .wait (NativeMutex.pollLock ⟨1⟩) (postAcquire value) := by
  rw [critical_contract]
  simp only [NativeMutex.lock, Result.wait_bind, bind_assoc]
  congr 1
  funext reply
  cases reply <;> simp [postAcquire, NativeM.ok]

private def afterWrite (guard : NativeGuard NativeFile) (start : U64) (amount : Usize) : Result Term :=
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

private theorem set_len_poll (before after : State) (length : U64) (counter : Nat) (contents : Term)
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

private theorem truncate_append (data bytes : ByteArray) (amount : Nat) :
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

end Record.RollbackProperties
