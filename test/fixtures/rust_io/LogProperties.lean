module
public import Record.AppendProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.LogProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties

/-- Evidence for the four actual file-model steps which decode one record.
No Rust contract is assumed: these are executable readStep equations. -/
inductive RecordStep (before after : State) (value : U16) : Prop where
  | mk
      (middle1 : State)
      (middle2 : State)
      (middle3 : State)
      (valid0 : Valid before)
      (valid1 : Valid middle1)
      (valid2 : Valid middle2)
      (valid3 : Valid middle3)
      (ready0 : blocked before = false)
      (ready1 : blocked middle1 = false)
      (ready2 : blocked middle2 = false)
      (ready3 : blocked middle3 = false)
      (read0 : readStep before (one 0#u8) = some (.Ok 1#usize, middle1, one (low value)))
      (read1 : readStep middle1 (one 0#u8) = some (.Ok 1#usize, middle2, one (high value)))
      (read2 : readStep middle2 (one 0#u8) = some (.Ok 1#usize, middle3, one (low (~~~value))))
      (read3 : readStep middle3 (one 0#u8) = some (.Ok 1#usize, after, one (high (~~~value)))) : RecordStep before after value

/-- A finite sequence of validated file operations, retaining intermediate
state rather than assuming a parser implementation or a pure file snapshot. -/
inductive Records : State → List U16 → State → Prop where
  | nil (state) : Records state [] state
  | cons (step : RecordStep before middle value)
      (tail : Records middle values after) : Records before (value :: values) after

theorem record_step_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State) (value : U16)
    (separate : Separate file frame) (step : RecordStep before after value)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next) (fileEnv env file before frame) =
      next (.Ok (some value), file) (fileEnv env file after frame) := by
  obtain ⟨s1, s2, s3, v0, v1, v2, v3, n0, n1, n2, n3, r0, r1, r2, r3⟩ := step
  exact record_next file env frame before s1 s2 s3 after value separate
    v0 v1 v2 v3 n0 n1 n2 n3 r0 r1 r2 r3 next

/-- Induction over the actual extracted loop, including its accumulated Vec,
mutable file state, capacity bound and verification fuel. -/
theorem loop_records (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (values : List U16) (trace : Records before values after)
    (accumulated : List U16) (maxRecords : Usize) (fuel : Nat)
    (separate : Separate file frame)
    (count : maxRecords.val = accumulated.length + values.length)
    (capacity : maxRecords.val ≤ 262144) (enough : values.length < fuel)
    (accumulatedValid : accumulated.length ≤ Usize.max) :
    NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
      fuel (file, alloc.vec.Vec.from accumulated accumulatedValid) (fileEnv env file before frame) =
      (.ok (.Ok (alloc.vec.Vec.from (accumulated ++ values) (by simp; scalar_tac)), file),
        fileEnv env file after frame) := by
  induction trace generalizing accumulated fuel with
  | nil state =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have stop : ¬(alloc.vec.Vec.from accumulated accumulatedValid).len < maxRecords := by
        simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv]
        simp only [Usize.ofNatCore, UScalar.ofNatCore_val_eq]
        simp only [List.length_nil, Nat.add_zero] at count
        omega
      simp only [NativeM.loopFuel, recover_log_loop.body, monadLift_self, stop, ite_false,
        NativeM.ok, Result.ok_bind, Result.ok_apply, List.append_nil]
  | @cons before middle value values after step tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have go : (alloc.vec.Vec.from accumulated accumulatedValid).len < maxRecords := by
        simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv]
        simp only [Usize.ofNatCore, UScalar.ofNatCore_val_eq]
        simp only [List.length_cons] at count
        omega
      rw [NativeM.loopFuel]
      simp only [recover_log_loop.body, monadLift_self, go, ite_true, bind_assoc]
      change (read_record file >>= _) _ = _
      rw [record_step_next file env frame before middle value separate step]
      simp only [NativeM.ok]
      rw [push_from accumulated value (by simp only [List.length_cons] at count; omega)]
      simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
      have recursion := ih (accumulated ++ [value]) fuel
        (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_cons] at enough; omega)
        (by simp; scalar_tac)
      simpa only [List.append_assoc, List.cons_append, List.nil_append, recover_log_loop.body, monadLift_self, NativeM.ok, NativeM.monadLift_eq] using recursion

/-- Recovery of any number of records within the declared capacity, grounded
in actual read operations after the actual cross-crate seek. -/
theorem recover_log_records (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before reset after : State)
    (values : List U16) (maxRecords : Usize)
    (separate : Separate file frame) (valid : Valid before)
    (ready : blocked before = false)
    (seek : seekStep before (.start 0#u64) = some (.Ok 0#u64, reset))
    (trace : Records reset values after)
    (count : maxRecords.val = values.length) (capacity : values.length ≤ 262144) :
    recover_log file maxRecords (fileEnv env file before frame) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        fileEnv env file after frame) := by
  simp only [recover_log, monadLift_self]
  rw [seek_next file 0#u64 env frame before reset (.Ok 0#u64) separate valid ready seek]
  simp only [recover_log_loop, monadLift_self, NativeM.loop]
  have result := loop_records file env frame reset after values trace [] maxRecords 262145
    separate (by simpa using count) (by omega) (by omega) (by simp)
  simpa only [alloc.vec.Vec.new, List.nil_append] using result

/-- Reading the next byte of an arbitrary bounded file with the declared
successful read script preserves all file bytes and advances one position. -/
theorem scanning_step (data : ByteArray) (rest : Term) (position : Nat)
    (byte : UInt8) (tail : List UInt8)
    (contents : data.data.toList.drop position = byte :: tail) :
    readStep (scanning data rest position) (one 0#u8) =
      some (.Ok 1#usize, scanning data rest (position + 1), one (byteValue byte)) := by
  have length := congrArg List.length contents
  simp only [List.length_drop, _root_.Array.length_toList, ByteArray.size_data,
    List.length_cons] at length
  have remains : data.size - position = (data.size - (position + 1)) + 1 := by omega
  have step := read_one_step (scanning data rest position) byte tail (zeroMask data) data
    (readScript (zeroMask data) (eofPlan data rest) (data.size - (position + 1)))
    contents (by simp [scanning, remains, readScript, action_outcome]) (persist_zero data)
  simpa only [readState, scanning] using step

@[expose] def logBytes (values : List U16) : List U8 := values.flatMap (fun value => (layout value).val)

@[simp] theorem logBytes_length (values : List U16) : (logBytes values).length = 4 * values.length := by
  induction values with
  | nil => rfl
  | cons value values ih =>
    simp only [logBytes, List.flatMap_cons, List.length_append, layout, Array.make_val,
      List.length_cons, List.length_nil, List.length_flatMap] at *
    omega

/-- Construct each parser obligation from the actual encoded bytes, at an
arbitrary record offset with an arbitrary byte prefix and tail. -/
theorem scanning_record (head tail : List U8) (value : U16) (rest : Term)
    (bounded : (head ++ (layout value).val ++ tail).length ≤ limit) :
    RecordStep (scanning (disk (head ++ (layout value).val ++ tail)) rest head.length)
      (scanning (disk (head ++ (layout value).val ++ tail)) rest (head.length + 4)) value := by
  let data := disk (head ++ (layout value).val ++ tail)
  have size : data.size = head.length + 4 + tail.length := by
    simp [data, disk, layout, ← ByteArray.size_data]
    omega
  have bound : data.size ≤ limit := by
    simpa [data, disk, ← ByteArray.size_data] using bounded
  have slice (n : Nat) : data.data.toList.drop (head.length + n) =
      (((layout value).val ++ tail).map rawByte).drop n := by
    rw [← List.drop_drop]
    have leading : data.data.toList.drop head.length = ((layout value).val ++ tail).map rawByte := by
      change ((head ++ (layout value).val ++ tail).map rawByte).drop head.length = _
      simp only [List.append_assoc, List.map_append]
      have h := List.drop_left (l₁ := head.map rawByte) (l₂ := ((layout value).val ++ tail).map rawByte)
      simpa only [List.length_map, List.map_append] using h
    rw [leading]
  have valid (n : Nat) (small : n ≤ 4) : Valid (scanning data rest (head.length + n)) := by
    simp only [Valid, scanning]
    exact ⟨bound, Nat.le_refl _, by omega⟩
  have ready (n : Nat) (small : n < 4) : blocked (scanning data rest (head.length + n)) = false := by
    have remaining : data.size - (head.length + n) =
        (data.size - (head.length + n + 1)) + 1 := by omega
    simp [scanning, remaining, readScript, blocked, outcome]
  change RecordStep (scanning data rest head.length) (scanning data rest (head.length + 4)) value
  refine RecordStep.mk (scanning data rest (head.length + 1))
    (scanning data rest (head.length + 2)) (scanning data rest (head.length + 3))
    (by simpa using valid 0 (by decide)) (valid 1 (by decide)) (valid 2 (by decide)) (valid 3 (by decide))
    (by simpa using ready 0 (by decide)) (ready 1 (by decide)) (ready 2 (by decide)) (ready 3 (by decide))
    ?_ ?_ ?_ ?_
  · simpa only [byte_roundtrip] using scanning_step data rest head.length
      (rawByte (low value)) _ (by simpa [layout] using slice 0)
  · simpa only [byte_roundtrip, Nat.add_assoc] using scanning_step data rest (head.length + 1)
      (rawByte (high value)) _ (by simpa [layout] using slice 1)
  · simpa only [byte_roundtrip, Nat.add_assoc] using scanning_step data rest (head.length + 2)
      (rawByte (low (~~~value))) _ (by simpa [layout] using slice 2)
  · simpa only [byte_roundtrip, Nat.add_assoc] using scanning_step data rest (head.length + 3)
      (rawByte (high (~~~value))) _ (by simpa [layout] using slice 3)

/-- Every record in a bounded encoded log supplies its own actual parser
obligations; no per-record assumptions are required from a caller. -/
theorem scanning_records (values : List U16) (head tail : List U8) (rest : Term)
    (bounded : (head ++ logBytes values ++ tail).length ≤ limit) :
    Records (scanning (disk (head ++ logBytes values ++ tail)) rest head.length) values
      (scanning (disk (head ++ logBytes values ++ tail)) rest (head.length + 4 * values.length)) := by
  induction values generalizing head with
  | nil => simpa [logBytes] using Records.nil (scanning (disk (head ++ tail)) rest head.length)
  | cons value values ih =>
    have step := scanning_record head (logBytes values ++ tail) value rest
      (by simpa only [logBytes, List.flatMap_cons, List.append_assoc] using bounded)
    have next := ih (head ++ (layout value).val)
      (by simpa only [logBytes, List.flatMap_cons, List.append_assoc] using bounded)
    apply Records.cons (middle := scanning (disk (head ++ logBytes (value :: values) ++ tail)) rest
      (head.length + 4))
    · simpa only [logBytes, List.flatMap_cons, List.append_assoc] using step
    · convert next using 1 <;>
        simp [logBytes, List.append_assoc, layout, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- For every bounded list of payloads the actual cross-crate recovery loop
returns exactly that list in order, after seeking from any valid initial offset.
All file reads are constructed from encoded bytes, rather than assumed. -/
theorem recover_encoded_log (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (rest : Term) (position : Nat)
    (separate : Separate file frame) (bounded : values.length ≤ 262144) (offset : position ≤ limit) :
    recover_log file (Usize.ofNatCore values.length (by scalar_tac))
      (fileEnv env file ⟨disk (logBytes values), disk (logBytes values), position,
        recoveryScript (disk (logBytes values)) rest⟩ frame) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        fileEnv env file (scanning (disk (logBytes values)) rest (4 * values.length)) frame) := by
  have size : (disk (logBytes values)).size = 4 * values.length := by
    simp [disk, ← ByteArray.size_data]
  apply recover_log_records file env frame _ (scanning (disk (logBytes values)) rest 0) _ values _
    separate
  · simp only [Valid, size]
    exact ⟨by simp only [limit]; omega, Nat.le_refl _, offset⟩
  · simp [blocked, recoveryScript, outcome]
  · simpa [scanning, recoveryScript, sought] using seek_start
      (⟨disk (logBytes values), disk (logBytes values), position,
        recoveryScript (disk (logBytes values)) rest⟩ : State)
      0#u64 (zeroMask (disk (logBytes values))) (disk (logBytes values)) _ (by simp [limit])
      (action_outcome _ _ _ _ _) (persist_zero _)
  · simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using
      scanning_records values [] [] rest (by simp [logBytes_length, limit]; omega)
  · simp [Usize.ofNatCore]
  · exact bounded

/-- Every admitted crash image of a synchronized encoded log is recovered by
the actual Rust loop, regardless of the number of records within the bound. -/
theorem stable_log_recovery (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State) (values : List U16)
    (mask : ByteArray) (image : Image) (rest : Term)
    (separate : Separate file frame) (valid : Valid state)
    (stable : state.durable = state.visible) (contents : state.visible = disk (logBytes values))
    (bounded : values.length ≤ 262144)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          (scanning image.bytes rest (4 * values.length)) []) := by
  have shape : image.bytes = disk (logBytes values) :=
    (stable_image file env frame state mask image separate valid stable captured).1.trans contents
  rw [restart_as_fileEnv]
  simpa only [shape] using recover_encoded_log (⟨image.highWater + 1⟩ : NativeFile)
    ({} : Environment) [] values rest 0 (by simp [Separate]) bounded (by simp [limit])

/-- One acknowledged append extends an arbitrary acknowledged encoded log;
every admitted subsequent crash recovers all old payloads followed by the new
one. This is an implementation-linked invariant step for a bounded log. -/
theorem append_log_recovery (file : NativeFile) (value : U16) (values : List U16)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (mask durable syncMask crashMask : ByteArray) (rest recoveryRest : Term) (image : Image)
    (separate : Separate file frame) (valid : Valid before)
    (contents : before.visible = disk (logBytes values)) (stable : before.durable = before.visible)
    (bounded : values.length < 262144)
    (script : before.script = outcome "seek" true 0 (zeroMask before.visible)
      (outcome "write" true 4 mask (outcome "sync_all" true 0 syncMask rest)))
    (accepted : persist before.visible
      (overwrite before.visible before.visible.size (bytes (payload value)) 4) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (appended before value rest) frame) = some image) :
    append_record file value (fileEnv env file before frame) =
      (.ok (.Ok true, file), fileEnv env file (appended before value rest) frame) ∧
    recover_log ⟨image.highWater + 1⟩
      (Usize.ofNatCore (values ++ [value]).length (by simp; scalar_tac))
      (restarted image (recoveryScript image.bytes recoveryRest)) =
      (.ok (.Ok (alloc.vec.Vec.from (values ++ [value]) (by simp; scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          (scanning image.bytes recoveryRest (4 * (values ++ [value]).length)) []) := by
  have fits : before.visible.size + 4 ≤ limit := by
    simp only [contents, disk, ByteArray.size, List.size_toArray, List.length_map, logBytes_length]
    simp only [limit]
    omega
  have proof := append_crash_prefix file value env frame before mask durable syncMask crashMask
    rest image separate valid stable fits script accepted captured
  have shape : image.bytes = disk (logBytes (values ++ [value])) := by
    apply ByteArray.ext
    apply _root_.Array.toList_inj.mp
    simpa [contents, logBytes, disk, encoded, fourBytes, layout, rawByte] using proof.2
  refine ⟨proof.1, ?_⟩
  rw [restart_as_fileEnv]
  simpa only [shape] using recover_encoded_log (⟨image.highWater + 1⟩ : NativeFile)
    ({} : Environment) [] (values ++ [value]) recoveryRest 0 (by simp [Separate])
    (by simp; omega) (by simp [limit])

end Record.LogProperties
