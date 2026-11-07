module
public import Record.TornConcurrent
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.WriteInterrupted
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.LockedProperties Record.LockedConcurrent Record.RepairCrashProperties
open Record.RollbackProperties (postAcquire afterWrite worker_wait)
open Record.InterruptedProperties (blocked_prefix)
open Record.TornConcurrent (overwrite_log_image crash_shared_image tail_write tail_size)

@[expose] def input (data : ByteArray) (position amount : Nat) (mask : ByteArray) (rest : Term) : State :=
  ⟨data, data, position, outcome "seek" true 0 (zeroMask data)
    (outcome "write" true amount mask (.cons (.atom "blocked") rest))⟩

@[expose] def pending (data : ByteArray) (value : U16) (durable : ByteArray)
    (amount : Nat) (rest : Term) : State :=
  ⟨overwrite data data.size (bytes (payload value)) amount,
    durable, data.size + amount, .cons (.atom "blocked") rest⟩

private theorem before_resize_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (fresh : 2 ≤ counter) (data : ByteArray) (value : U16) (position amount : Nat)
    (mask durable : ByteArray) (rest : Term) (fits : data.size + 4 ≤ limit)
    (offset : position ≤ limit) (short : amount < 4)
    (accepted : persist data (overwrite data data.size (bytes (payload value)) amount) mask = some durable) :
    Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (input data position amount mask rest))
      (shared counter (owned pid token) (pending data value durable amount rest)) := by
  let before := input data position amount mask rest
  let afterSeek := sought before data.size data (outcome "write" true amount mask (.cons (.atom "blocked") rest))
  let afterWrite := pending data value durable amount rest
  have bound : data.size ≤ limit := by omega
  have positionBound : data.size + amount ≤ limit := by omega
  have bounded : amount ≤ (payload value).val.length := by simp [payload, layout]; omega
  have valid0 : Valid before := ⟨bound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨bound, Nat.le_refl _, bound⟩
  have valid2 : Valid afterWrite := written_valid afterSeek (payload value) amount mask durable _
    valid1 bounded positionBound accepted
  let size := U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)
  let amountValue := count (payload value) amount bounded
  refine blocked_prefix pid peer token counter different before afterSeek afterWrite value size amountValue _ fresh
    valid0 valid1 (by simp [before, input, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, input, size] using
      seek_end_step before valid0 (zeroMask data) data _ (action_outcome _ _ _ _ _) (persist_zero data)
  · exact write_step afterSeek (payload value) amount mask durable _ bounded
      (by simp [payload, layout, limit]) positionBound (action_outcome _ _ _ _ _) accepted
  · have unequal : amountValue.val ≠ 4 := by
      simp only [amountValue, count, Usize.ofNatCore, UScalar.ofNatCore_val_eq]
      omega
    simp only [afterWrite]
    simp only [Record.RollbackProperties.afterWrite, resize_then_sync, io_core.resize_to,
      monadLift_self, bind_assoc, NativeFile.setLen, Result.wait_bind]
    refine .blocked _ _ _ ?_ ?_
    · intro env owner count heap
      have found : lookup (⟨2⟩ : NativeFile) env = some (pending data value durable amount rest) := by
        change env.refCounter = counter at count
        simp [lookup, count, heap, shared,
          decode_encode (pending data value durable amount rest) valid2]
        omega
      simp [pollSetLen, found, pending, blocked]
    · intro env owner _ heap
      exact held_blocked pid peer token counter _ different env owner heap

/-- A short write can block before truncation while retaining its visible and
durable tail. No future truncation or synchronization outcome is assumed. -/
theorem before_resize_stalls (data : ByteArray) (first second : U16)
    (position amount : Nat) (mask firstDurable secondDurable : ByteArray) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) (short : amount < 4)
    (firstWrite : persist data (overwrite data data.size (bytes (payload first)) amount) mask = some firstDurable)
    (secondWrite : persist data (overwrite data data.size (bytes (payload second)) amount) mask = some secondDurable)
    (choices : List ScheduleChoice) :
    let before := input data position amount mask rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 1 3) (pending data first firstDurable amount rest)) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 2 3) (pending data second secondDurable amount rest)) := by
  have result := Result.two_wait_blocked_orders
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨2⟩⟩))
    (shared 2 free (input data position amount mask rest))
    (shared 3 (owned 1 3) (input data position amount mask rest))
    (shared 3 (owned 1 3) (pending data first firstDurable amount rest))
    (shared 3 (owned 2 3) (input data position amount mask rest))
    (shared 3 (owned 2 3) (pending data second secondDurable amount rest))
    (lock_poll 1 2 _ (by decide)) (lock_poll 2 2 _ (by decide))
    (before_resize_trace 1 2 3 3 (by decide) (by decide) data first position amount mask firstDurable rest
      fits offset short firstWrite)
    (before_resize_trace 2 1 3 3 (by decide) (by decide) data second position amount mask secondDurable rest
      fits offset short secondWrite) choices
  simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared] using result

/-- Power loss before truncation may retain a partial visible/durable tail.
Every admitted image preserves the complete prefix, which fresh actual Rust
repair recovers without requiring the interrupted rollback to have run. -/
theorem before_resize_crash_repair (values : List U16) (first second : U16)
    (position amount : Nat) (writeMask firstDurable secondDurable : ByteArray)
    (rest recoveryRest : Term) (maxRecords : Usize)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (offset : position ≤ limit)
    (short : amount < 4) (more : values.length < maxRecords.val)
    (firstWrite : persist (disk (logBytes values))
      (overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload first)) amount)
      writeMask = some firstDurable)
    (secondWrite : persist (disk (logBytes values))
      (overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload second)) amount)
      writeMask = some secondDurable)
    (choices : List ScheduleChoice) (mask : ByteArray) (image : Image) :
    let data := disk (logBytes values)
    let before := input data position amount writeMask rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    crashImage ⟨2⟩ mask observed.2 = some image →
    observed.1 = .deadlock ∧ LogImage values image.bytes ∧
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
  have original : LogImage values data := by simpa using log_image values [] (by decide)
  have firstVisible := overwrite_log_image values first amount short
  have secondVisible := overwrite_log_image values second amount short
  have firstImage := persist_log_image values data _ writeMask firstDurable original firstVisible firstWrite
  have secondImage := persist_log_image values data _ writeMask secondDurable original secondVisible secondWrite
  have orders := before_resize_stalls data first second position amount writeMask firstDurable secondDurable
    rest fits offset short firstWrite secondWrite choices
  rcases orders with equal | equal
  all_goals
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    have shape := crash_shared_image _ _ values _ mask image fits sharedFields.1 sharedFields.2
      (by dsimp [pending]; omega)
      (by first | exact firstVisible | exact secondVisible)
      (by first | exact firstImage | exact secondImage) captured
    exact ⟨fields.1, shape.1, restart_repair values image recoveryRest maxRecords shape.1 shape.2 more⟩

private theorem capture_written_tail (env : Environment) (pid : Nat) (value : U16) (rest : Term)
    (counter : env.refCounter = 3)
    (heap : env.nativeHeap =
      (shared 3 (owned pid 3) (pending ByteArray.empty value (crop (encoded value) 2) 2 rest)).2) :
    crashImage ⟨2⟩ ⟨#[0, 0]⟩ env = some (⟨crop (encoded value) 2, 3⟩ : Image) := by
  have valid : Admitted (pending ByteArray.empty value (crop (encoded value) 2) 2 rest) := by
    simp [Admitted, pending, payload_bytes, overwrite_empty, tail_size, limit]
  have persisted : persist (crop (encoded value) 2) (crop (encoded value) 2) ⟨#[0, 0]⟩ =
      some (crop (encoded value) 2) := by
    simpa [zeroMask, tail_size, _root_.Array.replicate_succ] using persist_zero (crop (encoded value) 2)
  unfold crashImage lookup
  rw [counter, heap]
  simp [shared, decode_admitted _ valid]
  simp [pending, payload_bytes, overwrite_empty, persisted]

/-- A concrete admitted short write retains both visible and durable bytes
before any truncation. The image comes from the actual first owner's encoding,
with no future IO or caller-supplied transition equations. -/
theorem before_resize_images (first second : U16) (rest : Term) (choices : List ScheduleChoice) :
    let before := input ByteArray.empty 0 2 ⟨#[1, 1]⟩ rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, crashImage ⟨2⟩ ⟨#[0, 0]⟩ observed.2) =
        (.deadlock, some (⟨crop (encoded first) 2, 3⟩ : Image)) ∨
    (observed.1, crashImage ⟨2⟩ ⟨#[0, 0]⟩ observed.2) =
        (.deadlock, some (⟨crop (encoded second) 2, 3⟩ : Image)) := by
  dsimp only
  have orders := before_resize_stalls ByteArray.empty first second 0 2 ⟨#[1, 1]⟩
    (crop (encoded first) 2) (crop (encoded second) 2) rest
    (by decide) (by decide) (by decide) (tail_write first) (tail_write second) choices
  rcases orders with equal | equal
  · left
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    exact Prod.ext fields.1 (capture_written_tail _ 1 first rest sharedFields.1 sharedFields.2)
  · right
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    exact Prod.ext fields.1 (capture_written_tail _ 2 second rest sharedFields.1 sharedFields.2)

end Record.WriteInterrupted
