module
public import Record.CompleteRecovery
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.FullWriteConcurrent
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.LockedProperties Record.LockedConcurrent Record.RepairCrashProperties
  Record.CompleteRecovery
open Record.RollbackProperties (postAcquire afterWrite worker_wait)
open Record.InterruptedProperties (blocked_prefix)

@[expose] def input (data : ByteArray) (position : Nat) (mask : ByteArray) (rest : Term) : State :=
  ⟨data, data, position, outcome "seek" true 0 (zeroMask data)
    (outcome "write" true 4 mask (.cons (.atom "blocked") rest))⟩

@[expose] def pending (data : ByteArray) (value : U16) (durable : ByteArray) (rest : Term) : State :=
  ⟨overwrite data data.size (bytes (payload value)) 4, durable, data.size + 4, .cons (.atom "blocked") rest⟩

private theorem full_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (fresh : 2 ≤ counter) (data : ByteArray) (value : U16) (position : Nat)
    (mask durable : ByteArray) (rest : Term) (fits : data.size + 4 ≤ limit)
    (offset : position ≤ limit)
    (accepted : persist data (overwrite data data.size (bytes (payload value)) 4) mask = some durable) :
    Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (input data position mask rest))
      (shared counter (owned pid token) (pending data value durable rest)) := by
  let before := input data position mask rest
  let afterSeek := sought before data.size data (outcome "write" true 4 mask (.cons (.atom "blocked") rest))
  let written := pending data value durable rest
  have bound : data.size ≤ limit := by omega
  have valid0 : Valid before := ⟨bound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨bound, Nat.le_refl _, bound⟩
  have valid2 : Valid written := written_valid afterSeek (payload value) 4 mask durable _
    valid1 (by simp [payload, layout]) fits accepted
  let size := U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)
  refine blocked_prefix pid peer token counter different before afterSeek written value size 4#usize _ fresh
    valid0 valid1 (by simp [before, input, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, input, size] using
      seek_end_step before valid0 (zeroMask data) data _ (action_outcome _ _ _ _ _) (persist_zero data)
  · exact write_step afterSeek (payload value) 4 mask durable _ (by simp [payload, layout])
      (by simp [payload, layout, limit]) fits (action_outcome _ _ _ _ _) accepted
  · simp only [afterWrite, NativeFile.syncAll, Result.wait_bind]
    refine .blocked _ _ _ ?_ ?_
    · intro env owner count heap
      change env.refCounter = counter at count
      change env.nativeHeap = (shared counter (owned pid token) (pending data value durable rest)).2 at heap
      have found : lookup (⟨2⟩ : NativeFile) env = some (pending data value durable rest) := by
        simp [lookup, count, heap, shared, decode_encode (pending data value durable rest) valid2]
        omega
      simp [pollSync, found, pending, blocked]
    · intro env owner _ heap
      exact held_blocked pid peer token counter _ different env owner heap

/-- Full writes remain unacknowledged when synchronization blocks. Both owner
orders retain the complete visible record and admitted durable image. -/
theorem full_write_stalls (data : ByteArray) (first second : U16) (position : Nat)
    (mask firstDurable secondDurable : ByteArray) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit)
    (firstWrite : persist data (overwrite data data.size (bytes (payload first)) 4) mask = some firstDurable)
    (secondWrite : persist data (overwrite data data.size (bytes (payload second)) 4) mask = some secondDurable)
    (choices : List ScheduleChoice) :
    let before := input data position mask rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 1 3) (pending data first firstDurable rest)) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 2 3) (pending data second secondDurable rest)) := by
  have result := Result.two_wait_blocked_orders
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨2⟩⟩))
    (shared 2 free (input data position mask rest))
    (shared 3 (owned 1 3) (input data position mask rest)) (shared 3 (owned 1 3) (pending data first firstDurable rest))
    (shared 3 (owned 2 3) (input data position mask rest)) (shared 3 (owned 2 3) (pending data second secondDurable rest))
    (lock_poll 1 2 _ (by decide)) (lock_poll 2 2 _ (by decide))
    (full_trace 1 2 3 3 (by decide) (by decide) data first position mask firstDurable rest fits offset firstWrite)
    (full_trace 2 1 3 3 (by decide) (by decide) data second position mask secondDurable rest fits offset secondWrite) choices
  simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared] using result

private theorem capture_append (env : Environment) (pid : Nat) (values : List U16) (value : U16)
    (state : State) (mask : ByteArray) (image : Image)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (counter : env.refCounter = 3)
    (heap : env.nativeHeap = (shared 3 (owned pid 3) state).2)
    (offset : state.position ≤ limit) (visible : AppendImage values value state.visible)
    (durable : AppendImage values value state.durable)
    (captured : crashImage ⟨2⟩ mask env = some image) : AppendImage values value image.bytes := by
  have visibleBound : state.visible.size ≤ limit := by have bound := visible.2.1; omega
  have durableBound : state.durable.size ≤ limit := by have bound := durable.2.1; omega
  have valid : Admitted state := ⟨visibleBound, durableBound, offset⟩
  have found : lookup (⟨2⟩ : NativeFile) env = some state := by
    simp [lookup, counter, heap, shared, decode_admitted state valid]
  unfold crashImage at captured
  rw [found] at captured
  change (persist state.durable state.visible mask).bind
    (fun bytes => some (⟨bytes, env.refCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  exact persist_append_image values value _ _ _ _ durable visible accepted

/-- Crash before full-write acknowledgment. Every admitted image has a ready
actual Rust repair execution retaining the acknowledged prefix, optionally with
the actual first owner's unacknowledged value, and synchronized resulting bytes. -/
theorem full_write_crash_repair (values : List U16) (first second : U16) (position : Nat)
    (writeMask firstDurable secondDurable : ByteArray) (rest recoveryRest : Term) (maxRecords : Usize)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (offset : position ≤ limit)
    (more : values.length + 1 < maxRecords.val)
    (firstWrite : persist (disk (logBytes values))
      (overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload first)) 4) writeMask = some firstDurable)
    (secondWrite : persist (disk (logBytes values))
      (overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload second)) 4) writeMask = some secondDurable)
    (choices : List ScheduleChoice) (mask : ByteArray) (image : Image) :
    let data := disk (logBytes values)
    let before := input data position writeMask rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    crashImage ⟨2⟩ mask observed.2 = some image →
    observed.1 = .deadlock ∧ ∃ value : U16, (value = first ∨ value = second) ∧
      ∃ recovered : alloc.vec.Vec U16,
        (recovered.val = values ∨ recovered.val = values ++ [value]) ∧
        ∃ script : Term, ∃ final : State,
          repair_log ⟨image.highWater + 1⟩ maxRecords (restarted image script) =
            (.ok (.Ok (some recovered), ⟨image.highWater + 1⟩),
              fileEnv ({} : Environment) ⟨image.highWater + 1⟩ final []) ∧
          final.durable = final.visible ∧ Prefix (disk (logBytes values)) final.durable := by
  dsimp only
  intro captured
  let data := disk (logBytes values)
  have capacity : data.size + 4 ≤ limit := fits
  have firstVisible := complete_write_image values first
  have secondVisible := complete_write_image values second
  have firstImage := persist_append_image values first data _ writeMask firstDurable
    (original_image values first) firstVisible firstWrite
  have secondImage := persist_append_image values second data _ writeMask secondDurable
    (original_image values second) secondVisible secondWrite
  have orders := full_write_stalls data first second position writeMask firstDurable secondDurable rest
    fits offset firstWrite secondWrite choices
  rcases orders with equal | equal
  · have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    have imageShape := capture_append _ _ values first _ mask image fits sharedFields.1 sharedFields.2
      (by dsimp [pending]; omega) firstVisible firstImage captured
    exact ⟨fields.1, first, Or.inl rfl, repair_append_image values first image recoveryRest maxRecords imageShape fits more⟩
  · have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    have imageShape := capture_append _ _ values second _ mask image fits sharedFields.1 sharedFields.2
      (by dsimp [pending]; omega) secondVisible secondImage captured
    exact ⟨fields.1, second, Or.inr rfl, repair_append_image values second image recoveryRest maxRecords imageShape fits more⟩

private theorem written_encoded (value : U16) :
    overwrite ByteArray.empty 0 (bytes (payload value)) 4 = encoded value := by
  rw [payload_bytes, overwrite_empty]
  simp [crop, encoded, fourBytes]

private theorem capture_complete (env : Environment) (pid : Nat) (value : U16) (rest : Term)
    (counter : env.refCounter = 3)
    (heap : env.nativeHeap = (shared 3 (owned pid 3) (pending ByteArray.empty value (encoded value) rest)).2) :
    crashImage ⟨2⟩ (zeroMask (encoded value)) env = some (⟨encoded value, 3⟩ : Image) := by
  have valid : Admitted (pending ByteArray.empty value (encoded value) rest) := by
    simp [Admitted, pending, written_encoded, encoded, fourBytes, limit, ← ByteArray.size_data]
  unfold crashImage lookup
  rw [counter, heap]
  simp [shared, decode_admitted _ valid]
  simp [pending, written_encoded, persist_zero]

/-- A complete record may survive power loss before sync acknowledgment. Both
callers use the arbitrary same value so every finite schedule captures it;
the actual Rust repair then returns that value, rather than the prior empty log. -/
theorem surviving_full_record (value : U16) (rest : Term) (choices : List ScheduleChoice) :
    ∃ writeMask : ByteArray,
    let before := input ByteArray.empty 0 writeMask rest
    let worker := (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule worker .ok; worker : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    observed.1 = .deadlock ∧
    crashImage ⟨2⟩ (zeroMask (encoded value)) observed.2 = some (⟨encoded value, 3⟩ : Image) ∧
    ∃ script : Term,
      repair_log ⟨4⟩ 2#usize (restarted (⟨encoded value, 3⟩ : Image) script) =
        (.ok (.Ok (some (alloc.vec.Vec.from [value] (by scalar_tac))), ⟨4⟩),
          fileEnv ({} : Environment) ⟨4⟩ ⟨encoded value, encoded value, (encoded value).size, rest⟩ []) := by
  obtain ⟨mask, accepted⟩ := Record.TornConcurrent.visible_choice ByteArray.empty (encoded value)
  refine ⟨mask, ?_⟩
  dsimp only
  have write : persist ByteArray.empty (overwrite ByteArray.empty ByteArray.empty.size (bytes (payload value)) 4)
      mask = some (encoded value) := by simpa [written_encoded] using accepted
  have orders := full_write_stalls ByteArray.empty value value 0 mask (encoded value) (encoded value) rest
    (by decide) (by decide) write write choices
  have shape : LogImage [value] (encoded value) := by
    simpa [logBytes, disk, layout, encoded, fourBytes, rawByte] using log_image [value] [] (by decide)
  have recovery := restart_repair [value] (⟨encoded value, 3⟩ : Image) rest 2#usize shape
    (by simp [encoded, fourBytes, limit, ← ByteArray.size_data]) (by simp)
  rcases orders with equal | equal
  all_goals
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    refine ⟨fields.1, ?_,
      outcome "seek" true 0 (zeroMask (encoded value))
        (reader (encoded value) (outcome "set_len" true 0 (zeroMask (encoded value))
          (outcome "sync_all" true 0 ByteArray.empty rest)) 0).script, ?_⟩
    · exact capture_complete _ _ value rest sharedFields.1 sharedFields.2
    · simpa [logBytes, disk, layout, encoded, fourBytes, rawByte] using recovery

end Record.FullWriteConcurrent
