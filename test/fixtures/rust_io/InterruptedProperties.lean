module
public import Record.RollbackProperties
public import Record.RepairCrashProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.InterruptedProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.LockedProperties Record.LockedConcurrent Record.RepairCrashProperties
open Record.RollbackProperties (postAcquire afterWrite worker_wait set_len_poll)

private theorem blocked_prefix (pid peer token counter : Nat) (different : pid ≠ peer)
    (before sought written : State) (value : U16) (position : U64) (amount : Usize)
    (final : Nat × List (Nat × String × Term)) (fresh : 2 ≤ counter)
    (valid0 : Valid before) (valid1 : Valid sought)
    (ready0 : blocked before = false) (ready1 : blocked sought = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position, sought))
    (write : writeStep sought (payload value) = some (.Ok amount, written))
    (suffix : Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position amount)
      (shared counter (owned pid token) written) final) :
    Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) before) final := by
  simp only [postAcquire, recoverGuard]
  rw [Record.RollbackProperties.append_contract]
  simp only [bind_assoc, NativeFile.seek, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok position, (⟨2⟩ : NativeFile))) _
    (shared counter (owned pid token) sought) _ ?_ ?_ ?_
  · intro env _ count heap
    exact seek_poll before sought position counter _ valid0 ready0 seek fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter before different env owner heap
  · simp only [Result.ok_bind, NativeFile.write, Result.wait_bind]
    refine .wait _ _ (.ok (.Ok amount, (⟨2⟩ : NativeFile))) _
      (shared counter (owned pid token) written) _ ?_ ?_ ?_
    · intro env _ count heap
      exact write_result_poll sought written value (.Ok amount) counter _ valid1 ready1 write fresh env count heap
    · intro env owner _ heap
      exact held_blocked pid peer token counter sought different env owner heap
    · simp only [Result.ok_bind]
      exact suffix

@[expose] def stopped (data : ByteArray) (amount : Nat) (rest : Term) : State :=
  ⟨data, data, data.size + amount, .cons (.atom "blocked") rest⟩

@[expose] def interruptInput (data : ByteArray) (position amount : Nat) (rest : Term) : State :=
  ⟨data, data, position, outcome "seek" true 0 (zeroMask data)
    (outcome "write" true amount (zeroMask data)
      (outcome "set_len" true 0 (zeroMask data) (.cons (.atom "blocked") rest)))⟩

private theorem short_stopped (pid peer token counter : Nat) (different : pid ≠ peer)
    (written resized : State) (position : U64) (amount : Usize)
    (short : amount.val ≠ 4) (fresh : 2 ≤ counter) (valid0 : Valid written)
    (valid1 : Valid resized) (ready : blocked written = false)
    (truncate : setLenStep written position = some (.Ok (), resized))
    (blockedSync : blocked resized = true) :
    Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (afterWrite ⟨⟨1⟩, token, pid, ⟨2⟩⟩ position amount)
      (shared counter (owned pid token) written) (shared counter (owned pid token) resized) := by
  simp only [afterWrite]
  simp only [resize_then_sync, io_core.resize_to, io_core.synchronize, monadLift_self,
    bind_assoc, NativeFile.setLen, Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (shared counter (owned pid token) resized) _ ?_ ?_ ?_
  · intro env _ count heap
    exact set_len_poll written resized position counter _ valid0 ready truncate fresh env count heap
  · intro env owner _ heap
    exact held_blocked pid peer token counter written different env owner heap
  · simp only [Result.ok_bind, NativeFile.syncAll, Result.wait_bind]
    refine .blocked _ _ _ ?_ ?_
    · intro env owner count heap
      have found : lookup (⟨2⟩ : NativeFile) env = some resized := by
        simp [lookup, count, heap, shared, decode_encode resized valid1]
        omega
      simp [pollSync, found, blockedSync]
    · intro env owner _ heap
      exact held_blocked pid peer token counter resized different env owner heap

private theorem interrupted_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (fresh : 2 ≤ counter) (data : ByteArray) (value : U16) (position amount : Nat) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) (short : amount < 4) :
    Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (interruptInput data position amount rest))
      (shared counter (owned pid token) (stopped data amount rest)) := by
  let resizeRest := outcome "set_len" true 0 (zeroMask data) (.cons (.atom "blocked") rest)
  let before := interruptInput data position amount rest
  let afterSeek := sought before data.size data (outcome "write" true amount (zeroMask data) resizeRest)
  let afterWrite := written afterSeek (payload value) amount data resizeRest
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
  have valid3 : Valid (stopped data amount rest) := ⟨bound, Nat.le_refl _, positionBound⟩
  let size := U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)
  let amountValue := count (payload value) amount bounded
  refine blocked_prefix pid peer token counter different before afterSeek afterWrite value size amountValue _ fresh
    valid0 valid1 (by simp [before, interruptInput, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, interruptInput, resizeRest, size] using
      seek_end_step before valid0 (zeroMask data) data _ (action_outcome _ _ _ _ _) (persist_zero data)
  · exact write_step afterSeek (payload value) amount (zeroMask data) data resizeRest
      bounded (by simp [payload, layout, limit]) positionBound (action_outcome _ _ _ _ _) accepted
  · refine short_stopped pid peer token counter different afterWrite (stopped data amount rest) size amountValue
      (by simp only [amountValue, count, Usize.ofNatCore, UScalar.ofNatCore_val_eq]; omega)
      fresh valid2 valid3 (by simp [afterWrite, written, resizeRest, blocked, outcome]) ?_
      (by simp [stopped, blocked])
    simp [setLenStep, size, U64.ofNatCore, afterWrite, written, afterSeek, sought, resizeRest,
      action_outcome, before, interruptInput, Record.RollbackProperties.truncate_append, stopped,
      not_lt.mpr bound, persist_zero]

/-- The first owner stalls at rollback synchronization. Its peer remains locked
out under every finite scheduler choice list; no successful return is invented. -/
theorem concurrent_rollback_stalls (data : ByteArray) (first second : U16)
    (position amount : Nat) (rest : Term) (fits : data.size + 4 ≤ limit)
    (offset : position ≤ limit) (short : amount < 4) (choices : List ScheduleChoice) :
    let before := interruptInput data position amount rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 1 3) (stopped data amount rest)) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 2 3) (stopped data amount rest)) := by
  have result := Result.two_wait_blocked_orders
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨2⟩⟩))
    (shared 2 free (interruptInput data position amount rest))
    (shared 3 (owned 1 3) (interruptInput data position amount rest))
    (shared 3 (owned 1 3) (stopped data amount rest))
    (shared 3 (owned 2 3) (interruptInput data position amount rest))
    (shared 3 (owned 2 3) (stopped data amount rest))
    (lock_poll 1 2 _ (by decide)) (lock_poll 2 2 _ (by decide))
    (interrupted_trace 1 2 3 3 (by decide) (by decide) data first position amount rest fits offset short)
    (interrupted_trace 2 1 3 3 (by decide) (by decide) data second position amount rest fits offset short)
    choices
  simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared] using result

/-- A concrete accepted power-loss choice witnesses image capture from the
actual stalled execution; neither contention nor blocking erases the file. -/
theorem concurrent_crash_image (data : ByteArray) (first second : U16)
    (position amount : Nat) (rest : Term) (fits : data.size + 4 ≤ limit)
    (offset : position ≤ limit) (short : amount < 4) (choices : List ScheduleChoice) :
    let before := interruptInput data position amount rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, crashImage ⟨2⟩ (zeroMask data) observed.2) =
      (.deadlock, some (⟨data, 3⟩ : Image)) := by
  dsimp only
  have orders := concurrent_rollback_stalls data first second position amount rest fits offset short choices
  have valid : Valid (stopped data amount rest) :=
    ⟨by dsimp [stopped]; omega, Nat.le_refl _, by dsimp [stopped]; omega⟩
  rcases orders with equal | equal
  all_goals
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    rw [fields.1]
    unfold crashImage lookup
    rw [sharedFields.1, sharedFields.2]
    simp [decode_encode _ valid]
    simp [stopped, persist_zero]

private theorem crash_stopped (env : Environment) (pid : Nat) (data : ByteArray)
    (amount : Nat) (rest : Term) (mask : ByteArray) (image : Image)
    (valid : Valid (stopped data amount rest)) (counter : env.refCounter = 3)
    (heap : env.nativeHeap = (shared 3 (owned pid 3) (stopped data amount rest)).2)
    (captured : crashImage ⟨2⟩ mask env = some image) : image.bytes = data := by
  have found : lookup (⟨2⟩ : NativeFile) env = some (stopped data amount rest) := by
    simp [lookup, counter, heap, shared, decode_encode _ valid]
  unfold crashImage at captured
  rw [found] at captured
  change (persist data data mask).bind (fun bytes => some (⟨bytes, env.refCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  exact persist_same data mask bytes accepted

/-- Crash a stalled two-caller execution and discard its still-held mutex.
Every admitted power-loss mask retains the acknowledged complete prefix;
fresh actual Rust repair recovers exactly that prefix and synchronizes it. -/
theorem concurrent_crash_repair (values : List U16) (first second : U16)
    (position amount : Nat) (rest recoveryRest : Term) (maxRecords : Usize)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (offset : position ≤ limit)
    (short : amount < 4) (more : values.length < maxRecords.val)
    (choices : List ScheduleChoice) (mask : ByteArray) (image : Image) :
    let data := disk (logBytes values)
    let before := interruptInput data position amount rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    crashImage ⟨2⟩ mask observed.2 = some image →
    observed.1 = .deadlock ∧ image.bytes = data ∧
    repair_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes (outcome "set_len" true 0 (zeroMask image.bytes)
          (outcome "sync_all" true 0 ByteArray.empty recoveryRest)) 0).script)) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨data, data, image.bytes.size, recoveryRest⟩ []) := by
  dsimp only
  intro captured
  let data := disk (logBytes values)
  have capacity : data.size + 4 ≤ limit := fits
  have orders := concurrent_rollback_stalls data first second position amount rest fits offset short choices
  have valid : Valid (stopped data amount rest) := ⟨by dsimp [stopped]; omega, Nat.le_refl _, by dsimp [stopped]; omega⟩
  rcases orders with equal | equal
  all_goals
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    have bytes := crash_stopped _ _ data amount rest mask image valid sharedFields.1 sharedFields.2 captured
    refine ⟨fields.1, bytes, ?_⟩
    have shape : LogImage values image.bytes := by
      rw [bytes]
      simpa only [List.append_nil] using log_image values [] (by decide)
    have bounded : image.bytes.size ≤ limit := by rw [bytes]; omega
    simpa only [bytes] using restart_repair values image recoveryRest maxRecords shape bounded more

end Record.InterruptedProperties
