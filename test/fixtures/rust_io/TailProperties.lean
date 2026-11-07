module
public import Record.LogProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.TailProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties Record.LogProperties

/-- Transport an arbitrary finite prefix through the actual extracted loop.
The remaining computation is retained, including errors, waits and exhaustion. -/
theorem loop_prefix_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (values : List U16) (trace : Records before values after)
    (accumulated : List U16) (maxRecords : Usize) (fuel : Nat)
    (separate : Separate file frame)
    (count : accumulated.length + values.length ≤ maxRecords.val)
    (capacity : accumulated.length + values.length ≤ 262144)
    (enough : values.length ≤ fuel) (accumulatedValid : accumulated.length ≤ Usize.max)
    (next : core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile → NativeM α) :
    (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
      fuel (file, alloc.vec.Vec.from accumulated accumulatedValid) >>= next) (fileEnv env file before frame) =
    (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
      (fuel - values.length) (file, alloc.vec.Vec.from (accumulated ++ values) (by simp; scalar_tac)) >>= next)
      (fileEnv env file after frame) := by
  induction trace generalizing accumulated fuel with
  | nil state => simp
  | @cons before middle value values after step tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have go : (alloc.vec.Vec.from accumulated accumulatedValid).len < maxRecords := by
        simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv,
          Usize.ofNatCore, UScalar.ofNatCore_val_eq]
        simp only [List.length_cons] at count
        omega
      rw [NativeM.loopFuel]
      simp only [recover_log_loop.body, monadLift_self, go, ite_true, bind_assoc]
      change (read_record file >>= _) _ = _
      rw [record_step_next file env frame before middle value separate step]
      simp only [NativeM.ok]
      rw [push_from accumulated value (by simp only [List.length_cons] at capacity; omega)]
      simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
      have recursion := ih (accumulated ++ [value]) fuel
        (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_cons] at enough; omega) (by simp; scalar_tac)
      simpa only [List.append_assoc, List.cons_append, List.nil_append, List.length_cons,
        Nat.succ_sub_succ_eq_sub, recover_log_loop.body, monadLift_self, NativeM.ok,
        NativeM.monadLift_eq] using recursion

/-- Explicit EOF is available after the final byte, at every file size. -/
@[expose] def reader (data : ByteArray) (rest : Term) (position : Nat) : State :=
  ⟨data, data, position, readScript (zeroMask data)
    (outcome "read" true 0 (zeroMask data) rest) (data.size - position)⟩

theorem reader_valid (data : ByteArray) (rest : Term) (position : Nat)
    (bounded : data.size ≤ limit) (offset : position ≤ data.size) :
    Valid (reader data rest position) := by
  change data.size ≤ limit ∧ data.size ≤ data.size ∧ position ≤ limit
  exact ⟨bounded, Nat.le_refl _, by omega⟩

theorem reader_ready (data : ByteArray) (rest : Term) (position : Nat) :
    blocked (reader data rest position) = false := by
  unfold reader
  cases data.size - position <;> simp [readScript, blocked, outcome]

theorem reader_byte (data : ByteArray) (rest : Term) (position : Nat)
    (byte : U8) (tail : List U8)
    (contents : data.data.toList.drop position = (byte :: tail).map rawByte) :
    readStep (reader data rest position) (one 0#u8) =
      some (.Ok 1#usize, reader data rest (position + 1), one byte) := by
  have length := congrArg List.length contents
  simp only [List.length_drop, _root_.Array.length_toList, ByteArray.size_data,
    List.length_map, List.length_cons] at length
  have remains : data.size - position = (data.size - (position + 1)) + 1 := by omega
  have step := read_one_step (reader data rest position) (rawByte byte) (tail.map rawByte)
    (zeroMask data) data
    (readScript (zeroMask data) (outcome "read" true 0 (zeroMask data) rest) (data.size - (position + 1)))
    contents (by simp [reader, remains, readScript, action_outcome]) (persist_zero data)
  simpa only [readState, reader, byte_roundtrip] using step

theorem reader_eof (data : ByteArray) (rest : Term) :
    readStep (reader data rest data.size) (one 0#u8) =
      some (.Ok 0#usize, finished data rest, one 0#u8) := by
  simp [reader, readScript, readStep, action_outcome, persist_zero, finished, readBuffer,
    one, limit, Usize.ofNatCore]

/-- Reading an incomplete tail after an arbitrary prefix returns no record.
The original file contents and descriptor are retained; EOF is not a payload. -/
theorem truncated_at (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (head tail : List U8) (rest : Term)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (head ++ tail).length ≤ limit)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next) (fileEnv env file (reader (disk (head ++ tail)) rest head.length) frame) =
      next (.Ok none, file) (fileEnv env file (finished (disk (head ++ tail)) rest) frame) := by
  let data := disk (head ++ tail)
  have size : data.size = head.length + tail.length := by simp [data, disk, ← ByteArray.size_data]
  have bound : data.size ≤ limit := by simpa [size] using bounded
  have slice (n : Nat) : data.data.toList.drop (head.length + n) = (tail.map rawByte).drop n := by
    rw [← List.drop_drop]
    have initial : data.data.toList.drop head.length = tail.map rawByte := by
      change ((head ++ tail).map rawByte).drop head.length = _
      simpa only [List.map_append, List.length_map] using
        (List.drop_left (l₁ := head.map rawByte) (l₂ := tail.map rawByte))
    rw [initial]
  have valid (n : Nat) (small : n ≤ tail.length) := reader_valid data rest (head.length + n) bound (by omega)
  have eof : readStep (reader data rest (head.length + tail.length)) (one 0#u8) =
      some (.Ok 0#usize, finished data rest, one 0#u8) := by rw [← size]; exact reader_eof data rest
  change (read_record file >>= next) (fileEnv env file (reader data rest head.length) frame) = _
  simp only [read_record, monadLift_self, bind_assoc]
  cases tail with
  | nil =>
    rw [word_first_eof_next file env frame _ (finished data rest) separate
      (by simpa using valid 0 (by simp)) (reader_ready ..) (by simpa using eof)]
    simp [NativeM.ok, data]
  | cons a tail =>
    cases tail with
    | nil =>
      rw [word_second_eof_next file env frame _ (reader data rest (head.length + 1))
        (finished data rest) a separate (by simpa using valid 0 (by simp)) (valid 1 (by simp))
        (reader_ready ..) (reader_ready ..)
        (reader_byte data rest head.length a [] (by simpa using slice 0)) (by simpa using eof)]
      simp [NativeM.ok, data]
    | cons b tail =>
      have first := reader_byte data rest head.length a (b :: tail) (by simpa using slice 0)
      have second := reader_byte data rest (head.length + 1) b tail (by simpa using slice 1)
      rw [word_next file env frame _ (reader data rest (head.length + 1))
        (reader data rest (head.length + 2)) a b separate
        (by simpa using valid 0 (by simp)) (valid 1 (by simp))
        (reader_ready ..) (reader_ready ..) first (by simpa only [Nat.add_assoc] using second)]
      simp only [bind_assoc]
      cases tail with
      | nil =>
        rw [word_first_eof_next file env frame _ (finished data rest) separate
          (valid 2 (by simp)) (reader_ready ..) (by simpa using eof)]
        simp [NativeM.ok, data]
      | cons c tail =>
        cases tail with
        | nil =>
          rw [word_second_eof_next file env frame _ (reader data rest (head.length + 3))
            (finished data rest) c separate (valid 2 (by simp)) (valid 3 (by simp))
            (reader_ready ..) (reader_ready ..)
            (by simpa only [Nat.add_assoc] using (reader_byte data rest (head.length + 2) c []
              (by simpa using slice 2))) (by simpa using eof)]
          simp [NativeM.ok, data]
        | cons d tail => simp only [List.length_cons] at short; omega

/-- A complete prefix is parsed with an explicit EOF action following the
remaining bytes, including when the prefix is empty. -/
theorem reader_records (values : List U16) (head tail : List U8) (rest : Term)
    (bounded : (head ++ logBytes values ++ tail).length ≤ limit) :
    Records (reader (disk (head ++ logBytes values ++ tail)) rest head.length) values
      (reader (disk (head ++ logBytes values ++ tail)) rest (head.length + 4 * values.length)) := by
  cases values with
  | nil => simpa [logBytes] using Records.nil (reader (disk (head ++ tail)) rest head.length)
  | cons value values =>
    have enough : 4 ≤ (disk (head ++ logBytes (value :: values) ++ tail)).size := by
      simp [disk, ← ByteArray.size_data, logBytes, layout]
      omega
    have trace := scanning_records (value :: values) head tail
      (outcome "read" true 0 (zeroMask (disk (head ++ logBytes (value :: values) ++ tail))) rest) bounded
    simpa only [scanning, eofPlan, not_lt.mpr enough, ite_false, reader] using trace

/-- Once the valid prefix has been accumulated, the actual loop stops at the
partial tail, retaining the prefix and the final file state. -/
theorem loop_truncated_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest : Term) (maxRecords : Usize) (fuel : Nat)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (more : values.length < maxRecords.val) (enough : 0 < fuel)
    (valid : values.length ≤ Usize.max)
    (next : core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile → NativeM α) :
    (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
      fuel (file, alloc.vec.Vec.from values valid) >>= next)
      (fileEnv env file (reader (disk (logBytes values ++ tail)) rest (4 * values.length)) frame) =
      next (.Ok (alloc.vec.Vec.from values valid), file)
        (fileEnv env file (finished (disk (logBytes values ++ tail)) rest) frame) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have go : (alloc.vec.Vec.from values valid).len < maxRecords := by
      simpa only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv,
        Usize.ofNatCore, UScalar.ofNatCore_val_eq] using more
    rw [NativeM.loopFuel]
    simp only [recover_log_loop.body, monadLift_self, go, ite_true, bind_assoc]
    change (read_record file >>= _) _ = _
    rw [← logBytes_length values]
    rw [truncated_at file env frame (logBytes values) tail rest separate short bounded]
    simp [NativeM.ok]

/-- Recover every complete record before any tail shorter than four bytes,
with an arbitrary larger record limit. No exact-length limit is needed to stop.
Every byte of the partial tail is allowed; it never becomes a recovered record. -/
theorem recover_truncated_log_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (next : core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile → NativeM α) :
    (recover_log file maxRecords >>= next) (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail)) rest 0).script⟩ frame) =
      next (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file)
        (fileEnv env file (finished (disk (logBytes values ++ tail)) rest) frame) := by
  let data := disk (logBytes values ++ tail)
  have size : data.size = 4 * values.length + tail.length := by
    simp [data, disk, ← ByteArray.size_data]
  have bound : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  have capacity : values.length ≤ 262144 := by
    simp only [List.length_append, logBytes_length, limit] at bounded
    omega
  simp only [recover_log, monadLift_self, bind_assoc]
  rw [seek_next file 0#u64 env frame _ (reader data rest 0) (.Ok 0#u64) separate]
  · simp only [recover_log_loop, monadLift_self, NativeM.loop]
    have trace : Records (reader data rest 0) values (reader data rest (4 * values.length)) := by
      simpa only [List.nil_append, List.length_nil, Nat.zero_add] using reader_records values [] tail rest bounded
    have transport := loop_prefix_next file env frame _ _ values trace [] maxRecords 262145 separate
      (by simp; omega) (by simp; omega) (by omega) (by simp) next
    simp only [List.nil_append, alloc.vec.Vec.new] at transport ⊢
    rw [transport]
    exact loop_truncated_next file env frame values tail rest maxRecords _ separate short bounded more (by omega) _ next
  · exact ⟨bound, Nat.le_refl _, offset⟩
  · simp [blocked, outcome]
  · simpa [reader, sought] using seek_start
      (⟨data, data, position, outcome "seek" true 0 (zeroMask data) (reader data rest 0).script⟩ : State)
      0#u64 (zeroMask data) data _ (by simp [limit]) (action_outcome _ _ _ _ _) (persist_zero _)

/-- Execute recovery independently, retaining the same implementation-linked
EOF property as the continuation form. -/
theorem recover_truncated_log (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val) :
    recover_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail)) rest 0).script⟩ frame) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        fileEnv env file (finished (disk (logBytes values ++ tail)) rest) frame) := by
  simpa [NativeM.ok] using recover_truncated_log_next file env frame values tail rest position maxRecords
    separate short bounded offset more (fun result => NativeM.ok result)

/-- Restarting a synchronized file with an incomplete tail recovers precisely
its complete prefix, for every admitted crash image. The tail is retained on
disk; this theorem does not claim repair or truncation. -/
theorem restart_truncated_log (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State)
    (values : List U16) (tail : List U8) (mask : ByteArray) (image : Image)
    (rest : Term) (maxRecords : Usize)
    (separate : Separate file frame) (valid : Valid state) (stable : state.durable = state.visible)
    (contents : state.visible = disk (logBytes values ++ tail)) (short : tail.length < 4)
    (more : values.length < maxRecords.val)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    recover_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes rest 0).script)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ (finished image.bytes rest) []) := by
  have shape : image.bytes = disk (logBytes values ++ tail) :=
    (stable_image file env frame state mask image separate valid stable captured).1.trans contents
  have bound : (logBytes values ++ tail).length ≤ limit := by
    simpa only [contents, disk, ByteArray.size, List.size_toArray, List.length_map] using valid.1
  rw [restart_as_fileEnv]
  simpa only [shape] using recover_truncated_log (⟨image.highWater + 1⟩ : NativeFile)
    ({} : Environment) [] values tail rest 0 maxRecords (by simp [Separate]) short bound (by simp [limit]) more

/-- Every byte-boundary state in the successful read scan has unchanged visible
and durable bytes. Crashing there and restarting the actual Rust recovery
returns the same complete prefix, without accepting the partial tail. -/
theorem retry_during_scan (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest recoveryRest : Term) (position : Nat) (maxRecords : Usize) (mask : ByteArray) (image : Image)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ (disk (logBytes values ++ tail)).size)
    (more : values.length < maxRecords.val)
    (captured : crashImage file mask (fileEnv env file
      (reader (disk (logBytes values ++ tail)) rest position) frame) = some image) :
    recover_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes recoveryRest 0).script)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ (finished image.bytes recoveryRest) []) := by
  apply restart_truncated_log file env frame _ values tail mask image recoveryRest maxRecords separate
    (reader_valid _ rest position (by simpa [disk, ← ByteArray.size_data] using bounded) offset)
    rfl rfl short more captured

end Record.TailProperties
