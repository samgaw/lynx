module
public import Record.InterruptedProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.TornConcurrent
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties
  Record.LockedProperties Record.LockedConcurrent Record.RepairCrashProperties
open Record.RollbackProperties (postAcquire afterWrite worker_wait)
open Record.InterruptedProperties (blocked_prefix short_stopped)

@[expose] def input (data : ByteArray) (position amount : Nat)
    (writeMask resizeMask : ByteArray) (rest : Term) : State :=
  ⟨data, data, position, outcome "seek" true 0 (zeroMask data)
    (outcome "write" true amount writeMask
      (outcome "set_len" true 0 resizeMask (.cons (.atom "blocked") rest)))⟩

@[expose] def pending (data durable : ByteArray) (amount : Nat) (rest : Term) : State :=
  ⟨data, durable, data.size + amount, .cons (.atom "blocked") rest⟩

private theorem torn_trace (pid peer token counter : Nat) (different : pid ≠ peer)
    (fresh : 2 ≤ counter) (data : ByteArray) (value : U16) (position amount : Nat)
    (writeMask resizeMask writtenDurable resizedDurable : ByteArray) (rest : Term)
    (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) (short : amount < 4)
    (writePersist : persist data (overwrite data data.size (bytes (payload value)) amount)
      writeMask = some writtenDurable)
    (resizePersist : persist writtenDurable data resizeMask = some resizedDurable) :
    Result.ExclusiveBlocked pid peer (NativeMutex.pollLock (α := NativeFile) ⟨1⟩)
      (postAcquire value (.ok (.Ok ⟨⟨1⟩, token, pid, ⟨2⟩⟩)))
      (shared counter (owned pid token) (input data position amount writeMask resizeMask rest))
      (shared counter (owned pid token) (pending data resizedDurable amount rest)) := by
  let resizeRest := outcome "set_len" true 0 resizeMask (.cons (.atom "blocked") rest)
  let before := input data position amount writeMask resizeMask rest
  let afterSeek := sought before data.size data (outcome "write" true amount writeMask resizeRest)
  let afterWrite := written afterSeek (payload value) amount writtenDurable resizeRest
  have bound : data.size ≤ limit := by omega
  have positionBound : data.size + amount ≤ limit := by omega
  have bounded : amount ≤ (payload value).val.length := by simp [payload, layout]; omega
  have valid0 : Valid before := ⟨bound, Nat.le_refl _, offset⟩
  have valid1 : Valid afterSeek := ⟨bound, Nat.le_refl _, bound⟩
  have valid2 := written_valid afterSeek (payload value) amount writeMask writtenDurable resizeRest valid1
    bounded positionBound writePersist
  have writtenBound : writtenDurable.size ≤ limit := Nat.le_trans valid2.2.1 valid2.1
  have sizes := persist_size writtenDurable data resizeMask resizedDurable resizePersist
  have valid3 : Admitted (pending data resizedDurable amount rest) := by
    change data.size ≤ limit ∧ resizedDurable.size ≤ limit ∧ data.size + amount ≤ limit
    exact ⟨bound, by omega, positionBound⟩
  let size := U64.ofNatCore data.size (by simp only [limit] at bound; scalar_tac)
  let amountValue := count (payload value) amount bounded
  refine blocked_prefix pid peer token counter different before afterSeek afterWrite value size amountValue _ fresh
    valid0 valid1 (by simp [before, input, blocked, outcome])
    (by simp [afterSeek, sought, blocked, outcome]) ?_ ?_ ?_
  · simpa only [afterSeek, before, input, resizeRest, size] using
      seek_end_step before valid0 (zeroMask data) data _ (action_outcome _ _ _ _ _) (persist_zero data)
  · exact write_step afterSeek (payload value) amount writeMask writtenDurable resizeRest
      bounded (by simp [payload, layout, limit]) positionBound (action_outcome _ _ _ _ _) writePersist
  · refine short_stopped pid peer token counter different afterWrite (pending data resizedDurable amount rest) size amountValue
      (by simp only [amountValue, count, Usize.ofNatCore, UScalar.ofNatCore_val_eq]; omega)
      fresh valid2 valid3 (by simp [afterWrite, written, resizeRest, blocked, outcome]) ?_
      (by simp [pending, blocked])
    simp [setLenStep, size, U64.ofNatCore, afterWrite, written, afterSeek, sought, resizeRest,
      action_outcome, before, input, Record.RollbackProperties.truncate_append, pending,
      not_lt.mpr bound, resizePersist]

/-- Every admitted write/truncation persistence choice retains the actual
owner's resulting disk state across all finite two-caller schedules. -/
theorem torn_rollback_stalls (data : ByteArray) (first second : U16)
    (position amount : Nat) (writeMask resizeMask firstWritten firstResized secondWritten secondResized : ByteArray)
    (rest : Term) (fits : data.size + 4 ≤ limit) (offset : position ≤ limit) (short : amount < 4)
    (firstWrite : persist data (overwrite data data.size (bytes (payload first)) amount) writeMask = some firstWritten)
    (firstResize : persist firstWritten data resizeMask = some firstResized)
    (secondWrite : persist data (overwrite data data.size (bytes (payload second)) amount) writeMask = some secondWritten)
    (secondResize : persist secondWritten data resizeMask = some secondResized)
    (choices : List ScheduleChoice) :
    let before := input data position amount writeMask resizeMask rest
    let worker := fun value : U16 => (do
      let reply ← locked_append_or_rollback ⟨1⟩ value
      finish reply : Result Term)
    let observed := (do let _ ← Result.schedule (worker second) .ok; worker first : Result Term)
      {refCounter := 2, nativeHeap := (shared 2 free before).2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 1 3) (pending data firstResized amount rest)) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) =
        (.deadlock, shared 3 (owned 2 3) (pending data secondResized amount rest)) := by
  have result := Result.two_wait_blocked_orders
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire first)
    (NativeMutex.pollLock (α := NativeFile) ⟨1⟩) (postAcquire second)
    (.ok (.Ok ⟨⟨1⟩, 3, 1, ⟨2⟩⟩)) (.ok (.Ok ⟨⟨1⟩, 3, 2, ⟨2⟩⟩))
    (shared 2 free (input data position amount writeMask resizeMask rest))
    (shared 3 (owned 1 3) (input data position amount writeMask resizeMask rest))
    (shared 3 (owned 1 3) (pending data firstResized amount rest))
    (shared 3 (owned 2 3) (input data position amount writeMask resizeMask rest))
    (shared 3 (owned 2 3) (pending data secondResized amount rest))
    (lock_poll 1 2 _ (by decide)) (lock_poll 2 2 _ (by decide))
    (torn_trace 1 2 3 3 (by decide) (by decide) data first position amount writeMask resizeMask firstWritten firstResized
      rest fits offset short firstWrite firstResize)
    (torn_trace 2 1 3 3 (by decide) (by decide) data second position amount writeMask resizeMask secondWritten secondResized
      rest fits offset short secondWrite secondResize) choices
  simpa only [worker_wait, Result.schedule_bind, Result.ok_bind, shared] using result

theorem overwrite_append (head tail : List U8) (amount : Nat) :
    overwrite (disk head) (disk head).size (disk tail) amount = disk (head ++ tail.take amount) := by
  by_cases zero : amount = 0
  · simp [overwrite, zero, disk]
  · simp [overwrite, zero, disk, ← ByteArray.size_data, ← List.map_take]

/-- The actual encoded short-write prefix cannot form another complete record. -/
theorem overwrite_log_image (values : List U16) (value : U16) (amount : Nat) (short : amount < 4) :
    LogImage values (overwrite (disk (logBytes values)) (disk (logBytes values)).size
      (bytes (payload value)) amount) := by
  have layoutBytes : bytes (payload value) = disk (layout value).val := by
    simp [bytes, payload, layout, disk, rawByte]
  rw [layoutBytes, overwrite_append]
  exact log_image values ((layout value).val.take amount) (by simp only [List.length_take]; omega)

/-- Capture any admitted partial-tail file state in the independently stored
shared file cell. Both visible and durable images must retain the same prefix. -/
theorem crash_shared_image (env : Environment) (pid : Nat) (values : List U16)
    (state : State) (mask : ByteArray) (image : Image)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (counter : env.refCounter = 3)
    (heap : env.nativeHeap = (shared 3 (owned pid 3) state).2)
    (offset : state.position ≤ limit) (visible : LogImage values state.visible)
    (durable : LogImage values state.durable)
    (captured : crashImage ⟨2⟩ mask env = some image) :
    LogImage values image.bytes ∧ image.bytes.size ≤ limit := by
  have visibleBound : state.visible.size ≤ limit := by have bound := visible.2; omega
  have durableBound : state.durable.size ≤ limit := by have bound := durable.2; omega
  have valid : Admitted state := ⟨visibleBound, durableBound, offset⟩
  have found : lookup (⟨2⟩ : NativeFile) env = some state := by
    simp [lookup, counter, heap, shared, decode_admitted state valid]
  unfold crashImage at captured
  rw [found] at captured
  change (persist state.durable state.visible mask).bind
    (fun bytes => some (⟨bytes, env.refCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  have shape := persist_log_image values state.durable state.visible mask bytes durable visible accepted
  exact ⟨shape, by dsimp only; have bound := shape.2; omega⟩

private theorem crash_pending (env : Environment) (pid : Nat) (values : List U16)
    (durable : ByteArray) (amount : Nat) (rest : Term) (mask : ByteArray) (image : Image)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (short : amount < 4)
    (durableImage : LogImage values durable) (counter : env.refCounter = 3)
    (heap : env.nativeHeap = (shared 3 (owned pid 3) (pending (disk (logBytes values)) durable amount rest)).2)
    (captured : crashImage ⟨2⟩ mask env = some image) :
    LogImage values image.bytes ∧ image.bytes.size ≤ limit := by
  apply crash_shared_image env pid values _ mask image fits counter heap
  · dsimp [pending]
    omega
  · simpa [pending] using log_image values [] (by decide)
  · exact durableImage
  · exact captured

/-- Arbitrary admitted write, shrink and power-loss persistence choices may
retain a torn tail. Fresh actual Rust repair still recovers exactly the complete
acknowledged prefix, for either owner and every finite scheduling choice list. -/
theorem torn_crash_repair (values : List U16) (first second : U16)
    (position amount : Nat) (writeMask resizeMask firstWritten firstResized secondWritten secondResized : ByteArray)
    (rest recoveryRest : Term) (maxRecords : Usize)
    (fits : (disk (logBytes values)).size + 4 ≤ limit) (offset : position ≤ limit)
    (short : amount < 4) (more : values.length < maxRecords.val)
    (firstWrite : persist (disk (logBytes values))
      (overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload first)) amount)
      writeMask = some firstWritten)
    (firstResize : persist firstWritten (disk (logBytes values)) resizeMask = some firstResized)
    (secondWrite : persist (disk (logBytes values))
      (overwrite (disk (logBytes values)) (disk (logBytes values)).size (bytes (payload second)) amount)
      writeMask = some secondWritten)
    (secondResize : persist secondWritten (disk (logBytes values)) resizeMask = some secondResized)
    (choices : List ScheduleChoice) (mask : ByteArray) (image : Image) :
    let data := disk (logBytes values)
    let before := input data position amount writeMask resizeMask rest
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
  have original : LogImage values data := by simpa using log_image values [] (by decide)
  have firstKept := persist_log_image values data _ writeMask firstWritten original
    (overwrite_log_image values first amount short) firstWrite
  have secondKept := persist_log_image values data _ writeMask secondWritten original
    (overwrite_log_image values second amount short) secondWrite
  have firstImage := persist_log_image values firstWritten data resizeMask firstResized firstKept original firstResize
  have secondImage := persist_log_image values secondWritten data resizeMask secondResized secondKept original secondResize
  have orders := torn_rollback_stalls data first second position amount writeMask resizeMask firstWritten firstResized
    secondWritten secondResized rest fits offset short firstWrite firstResize secondWrite secondResize choices
  rcases orders with equal | equal
  all_goals
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    have shape := crash_pending _ _ values _ amount rest mask image fits short
      (by first | exact firstImage | exact secondImage) sharedFields.1 sharedFields.2 captured
    exact ⟨fields.1, shape.1, restart_repair values image recoveryRest maxRecords shape.1 shape.2 more⟩

private def fullMask (bytes : ByteArray) : ByteArray := ⟨_root_.Array.replicate bytes.size 1⟩

private theorem persist_keep_visible (old visible : ByteArray) :
    persist old visible (fullMask visible) = some visible := by
  have conditions : min old.size visible.size ≤ (fullMask visible).size ∧
      (fullMask visible).size ≤ max old.size visible.size ∧
      ((fullMask visible).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [fullMask, ← ByteArray.size_data]
  unfold persist
  rw [ite_eq_left conditions]
  congr 1
  apply ByteArray.ext
  apply _root_.Array.ext
  · simp [fullMask]
  · intro i hi hj
    have inside : i < visible.size := by simpa only [ByteArray.size_data] using hj
    simp [fullMask, getElem!_pos, inside]
    rfl

/-- A concrete all-new persistence choice exists for any visible file image. -/
theorem visible_choice (old visible : ByteArray) : ∃ mask, persist old visible mask = some visible :=
  ⟨fullMask visible, persist_keep_visible old visible⟩

theorem tail_size (value : U16) : (crop (encoded value) 2).size = 2 := by
  simp [crop, encoded, fourBytes, ← ByteArray.size_data]

theorem tail_write (value : U16) :
    persist ByteArray.empty (overwrite ByteArray.empty 0 (bytes (payload value)) 2) ⟨#[1, 1]⟩ =
      some (crop (encoded value) 2) := by
  rw [payload_bytes, overwrite_empty]
  simpa [fullMask, tail_size, _root_.Array.replicate_succ] using persist_keep_visible ByteArray.empty (crop (encoded value) 2)

private theorem tail_keep (value : U16) :
    persist (crop (encoded value) 2) ByteArray.empty ⟨#[0, 0]⟩ = some (crop (encoded value) 2) := by
  simpa [zeroMask, tail_size, _root_.Array.replicate_succ] using persist_keep_old (crop (encoded value) 2) ByteArray.empty

private theorem capture_tail (env : Environment) (pid : Nat) (value : U16) (rest : Term)
    (counter : env.refCounter = 3)
    (heap : env.nativeHeap = (shared 3 (owned pid 3) (pending ByteArray.empty (crop (encoded value) 2) 2 rest)).2) :
    crashImage ⟨2⟩ ⟨#[0, 0]⟩ env = some (⟨crop (encoded value) 2, 3⟩ : Image) := by
  have valid : Admitted (pending ByteArray.empty (crop (encoded value) 2) 2 rest) := by
    simp [Admitted, pending, tail_size, limit]
  unfold crashImage lookup
  rw [counter, heap]
  simp [shared, decode_admitted _ valid]
  simp [pending, tail_keep]

/-- A concrete admitted execution persists a two-byte short tail. Truncation
only changes visible bytes; the tail survives power loss in either owner order,
for arbitrary record values and every finite scheduling choice list. -/
theorem persisted_tail_images (first second : U16) (rest : Term) (choices : List ScheduleChoice) :
    let before := input ByteArray.empty 0 2 ⟨#[1, 1]⟩ ⟨#[0, 0]⟩ rest
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
  have orders := torn_rollback_stalls ByteArray.empty first second 0 2 ⟨#[1, 1]⟩ ⟨#[0, 0]⟩
    (crop (encoded first) 2) (crop (encoded first) 2)
    (crop (encoded second) 2) (crop (encoded second) 2) rest
    (by decide) (by decide) (by decide) (tail_write first) (tail_keep first)
    (tail_write second) (tail_keep second) choices
  rcases orders with equal | equal
  · left
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    exact Prod.ext fields.1 (capture_tail _ 1 first rest sharedFields.1 sharedFields.2)
  · right
    have fields := Prod.mk.inj equal
    have sharedFields := Prod.mk.inj fields.2
    exact Prod.ext fields.1 (capture_tail _ 2 second rest sharedFields.1 sharedFields.2)

end Record.TornConcurrent
