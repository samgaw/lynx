module
public import Record.RepairCrashProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.MalformedProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties Record.RepairCrashProperties

/-- The read plan stops at the first malformed record, independently of the
file length. Bytes after that record are present but need not be read. -/
@[expose] def planned (data : ByteArray) (rest : Term) (stop position : Nat) : State :=
  ⟨data, data, position, readScript (zeroMask data) rest (stop - position)⟩

theorem planned_valid (data : ByteArray) (rest : Term) (stop position : Nat)
    (bounded : data.size ≤ limit) (offset : position ≤ data.size) :
    Valid (planned data rest stop position) := by
  change data.size ≤ limit ∧ data.size ≤ data.size ∧ position ≤ limit
  exact ⟨bounded, Nat.le_refl _, by omega⟩

theorem planned_ready (data : ByteArray) (rest : Term) (stop position : Nat)
    (remaining : position < stop) : blocked (planned data rest stop position) = false := by
  have length : stop - position = (stop - (position + 1)) + 1 := by omega
  simp [planned, length, readScript, blocked, outcome]

theorem planned_byte (data : ByteArray) (rest : Term) (stop position : Nat)
    (byte : U8) (tail : List U8) (remaining : position < stop)
    (contents : data.data.toList.drop position = (byte :: tail).map rawByte) :
    readStep (planned data rest stop position) (one 0#u8) =
      some (.Ok 1#usize, planned data rest stop (position + 1), one byte) := by
  have length : stop - position = (stop - (position + 1)) + 1 := by omega
  have step := read_one_step (planned data rest stop position) (rawByte byte) (tail.map rawByte)
    (zeroMask data) data (readScript (zeroMask data) rest (stop - (position + 1)))
    contents (by simp [planned, length, readScript, action_outcome]) (persist_zero data)
  simpa only [readState, planned, byte_roundtrip] using step

/-- Select the suffix at an arbitrary byte offset without discarding the full
file or assuming a parser result. -/
theorem disk_suffix (head tail : List U8) (n : Nat) :
    (disk (head ++ tail)).data.toList.drop (head.length + n) = (tail.map rawByte).drop n := by
  rw [← List.drop_drop]
  have leading : (disk (head ++ tail)).data.toList.drop head.length = tail.map rawByte := by
    change ((head ++ tail).map rawByte).drop head.length = _
    simpa only [List.map_append, List.length_map] using
      (List.drop_left (l₁ := head.map rawByte) (l₂ := tail.map rawByte))
  rw [leading]

theorem planned_record (head tail : List U8) (value : U16) (rest : Term) (stop : Nat)
    (bounded : (head ++ (layout value).val ++ tail).length ≤ limit)
    (remaining : head.length + 4 ≤ stop) :
    RecordStep (planned (disk (head ++ (layout value).val ++ tail)) rest stop head.length)
      (planned (disk (head ++ (layout value).val ++ tail)) rest stop (head.length + 4)) value := by
  let data := disk (head ++ (layout value).val ++ tail)
  have size : data.size = head.length + 4 + tail.length := by
    simp [data, disk, layout, ← ByteArray.size_data]
    omega
  have bound : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  have valid (n : Nat) (small : n ≤ 4) := planned_valid data rest stop (head.length + n) bound (by omega)
  have ready (n : Nat) (small : n < 4) := planned_ready data rest stop (head.length + n) (by omega)
  have slice (n : Nat) : data.data.toList.drop (head.length + n) =
      (((layout value).val ++ tail).map rawByte).drop n := by
    simpa only [data, List.append_assoc] using disk_suffix head ((layout value).val ++ tail) n
  change RecordStep (planned data rest stop head.length) (planned data rest stop (head.length + 4)) value
  refine RecordStep.mk (planned data rest stop (head.length + 1))
    (planned data rest stop (head.length + 2)) (planned data rest stop (head.length + 3))
    (by simpa using valid 0 (by decide)) (valid 1 (by decide)) (valid 2 (by decide)) (valid 3 (by decide))
    (by simpa using ready 0 (by decide)) (ready 1 (by decide)) (ready 2 (by decide)) (ready 3 (by decide))
    ?_ ?_ ?_ ?_
  · exact planned_byte data rest stop head.length (low value) (high value :: low (~~~value) :: high (~~~value) :: tail) (by omega) (by simpa [layout] using slice 0)
  · simpa only [Nat.add_assoc] using planned_byte data rest stop (head.length + 1) (high value) (low (~~~value) :: high (~~~value) :: tail)
      (by omega) (by simpa [layout] using slice 1)
  · simpa only [Nat.add_assoc] using planned_byte data rest stop (head.length + 2) (low (~~~value)) (high (~~~value) :: tail)
      (by omega) (by simpa [layout] using slice 2)
  · simpa only [Nat.add_assoc] using planned_byte data rest stop (head.length + 3) (high (~~~value)) tail
      (by omega) (by simpa [layout] using slice 3)

/-- The actual reader rejects a failed complement check at an arbitrary
record offset, leaving all subsequent file bytes unread. -/
theorem malformed_at (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (head tail : List U8) (a b c d : U8)
    (rest : Term) (stop : Nat) (separate : Separate file frame)
    (bounded : (head ++ [a,b,c,d] ++ tail).length ≤ limit)
    (remaining : head.length + 4 ≤ stop)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next).run
      (fileEnv env file (planned (disk (head ++ [a,b,c,d] ++ tail)) rest stop head.length) frame) =
      next (.Ok none, file)
        (fileEnv env file (planned (disk (head ++ [a,b,c,d] ++ tail)) rest stop (head.length + 4)) frame) := by
  let data := disk (head ++ [a,b,c,d] ++ tail)
  have size : data.size = head.length + 4 + tail.length := by
    simp [data, disk, ← ByteArray.size_data]
    omega
  have bound : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  have valid (n : Nat) (small : n ≤ 4) := planned_valid data rest stop (head.length + n) bound (by omega)
  have ready (n : Nat) (small : n < 4) := planned_ready data rest stop (head.length + n) (by omega)
  have slice (n : Nat) : data.data.toList.drop (head.length + n) =
      (([a,b,c,d] ++ tail).map rawByte).drop n := by
    simpa only [data, List.append_assoc] using disk_suffix head ([a,b,c,d] ++ tail) n
  change (read_record file >>= next).run (fileEnv env file (planned data rest stop head.length) frame) = _
  simp only [read_record, monadLift_self, bind_assoc]
  rw [word_next file env frame _ (planned data rest stop (head.length + 1))
    (planned data rest stop (head.length + 2)) a b separate
    (by simpa using valid 0 (by decide)) (valid 1 (by decide))
    (by simpa using ready 0 (by decide)) (ready 1 (by decide))
    (planned_byte data rest stop head.length a (b :: c :: d :: tail) (by omega) (by simpa using slice 0))
    (by simpa only [Nat.add_assoc] using planned_byte data rest stop (head.length + 1) b (c :: d :: tail) (by omega) (by simpa using slice 1))]
  simp only [bind_assoc]
  rw [word_next file env frame _ (planned data rest stop (head.length + 3))
    (planned data rest stop (head.length + 4)) c d separate (valid 2 (by decide)) (valid 3 (by decide))
    (ready 2 (by decide)) (ready 3 (by decide))
    (by simpa only [Nat.add_assoc] using planned_byte data rest stop (head.length + 2) c (d :: tail) (by omega) (by simpa using slice 2))
    (by simpa only [Nat.add_assoc] using planned_byte data rest stop (head.length + 3) d tail (by omega) (by simpa using slice 3))]
  simp [decode_spec, bad, NativeM.ok, data]

theorem planned_records (values : List U16) (head tail : List U8) (rest : Term) (stop : Nat)
    (bounded : (head ++ logBytes values ++ tail).length ≤ limit)
    (remaining : head.length + 4 * values.length ≤ stop) :
    Records (planned (disk (head ++ logBytes values ++ tail)) rest stop head.length) values
      (planned (disk (head ++ logBytes values ++ tail)) rest stop (head.length + 4 * values.length)) := by
  induction values generalizing head with
  | nil => simpa [logBytes] using Records.nil (planned (disk (head ++ tail)) rest stop head.length)
  | cons value values ih =>
    have step := planned_record head (logBytes values ++ tail) value rest stop
      (by simpa only [logBytes, List.flatMap_cons, List.append_assoc] using bounded)
      (by simp only [List.length_cons] at remaining; omega)
    have following := ih (head ++ (layout value).val)
      (by simpa only [logBytes, List.flatMap_cons, List.append_assoc] using bounded)
      (by simpa [layout, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using remaining)
    apply Records.cons (middle := planned (disk (head ++ logBytes (value :: values) ++ tail)) rest stop (head.length + 4))
    · simpa only [logBytes, List.flatMap_cons, List.append_assoc] using step
    · convert following using 1 <;>
        simp [logBytes, List.append_assoc, layout, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

@[expose] def suffixBytes (a b c d : U8) (tail : List U8) : List U8 := [a,b,c,d] ++ tail

/-- The actual loop retains accumulated records and stops on the first bad
record. Later file contents cannot become recovered values. -/
theorem loop_malformed_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8) (a b c d : U8)
    (rest : Term) (maxRecords : Usize) (fuel : Nat)
    (separate : Separate file frame)
    (bounded : (logBytes values ++ suffixBytes a b c d tail).length ≤ limit)
    (more : values.length < maxRecords.val) (enough : 0 < fuel)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX) (valid : values.length ≤ Usize.max)
    (next : core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile → NativeM α) :
    (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
      fuel (file, alloc.vec.Vec.from values valid) >>= next).run
      (fileEnv env file (planned (disk (logBytes values ++ suffixBytes a b c d tail)) rest
        (4 * values.length + 4) (4 * values.length)) frame) =
      next (.Ok (alloc.vec.Vec.from values valid), file)
        (fileEnv env file (planned (disk (logBytes values ++ suffixBytes a b c d tail)) rest
          (4 * values.length + 4) (4 * values.length + 4)) frame) := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have go : (alloc.vec.Vec.from values valid).len < maxRecords := by
      simpa only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv,
        Usize.ofNatCore, UScalar.ofNatCore_val_eq] using more
    rw [NativeM.loopFuel]
    simp only [recover_log_loop.body, monadLift_self, go, ite_true, bind_assoc]
    change (read_record file >>= _).run _ = _
    have malformed := malformed_at (α := α) file env frame (logBytes values) tail a b c d rest
      (4 * values.length + 4) separate
      (by simpa only [suffixBytes, List.append_assoc] using bounded)
      (by simp) bad
    simp only [logBytes_length, List.append_assoc] at malformed
    simp only [suffixBytes]
    rw [malformed]
    simp [NativeM.ok]

/-- Recovery of an arbitrary valid prefix followed by a full malformed record
and arbitrary remaining bytes, with the actual mutable offset and continuation. -/
theorem recover_malformed_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8) (a b c d : U8)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame)
    (bounded : (logBytes values ++ suffixBytes a b c d tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX)
    (next : core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile → NativeM α) :
    (recover_log file maxRecords >>= next).run (fileEnv env file
      ⟨disk (logBytes values ++ suffixBytes a b c d tail), disk (logBytes values ++ suffixBytes a b c d tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ suffixBytes a b c d tail)))
          (planned (disk (logBytes values ++ suffixBytes a b c d tail)) rest (4 * values.length + 4) 0).script⟩ frame) =
      next (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file)
        (fileEnv env file (planned (disk (logBytes values ++ suffixBytes a b c d tail)) rest
          (4 * values.length + 4) (4 * values.length + 4)) frame) := by
  let data := disk (logBytes values ++ suffixBytes a b c d tail)
  have bound : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  have capacity : values.length < 262144 := by
    simp only [List.length_append, logBytes_length, suffixBytes, List.length_cons, List.length_nil, limit] at bounded
    omega
  let stop := 4 * values.length + 4
  simp only [recover_log, monadLift_self, bind_assoc]
  rw [seek_next file 0#u64 env frame _ (planned data rest stop 0) (.Ok 0#u64) separate]
  · simp only [recover_log_loop, monadLift_self, NativeM.loop]
    have trace : Records (planned data rest stop 0) values (planned data rest stop (4 * values.length)) := by
      simpa only [List.nil_append, List.length_nil, Nat.zero_add] using
        planned_records values [] (suffixBytes a b c d tail) rest stop bounded (by simp [stop])
    have transport := loop_prefix_next file env frame _ _ values trace [] maxRecords 262145 separate
      (by simp; omega) (by simp; omega) (by omega) (by simp) next
    simp only [List.nil_append, alloc.vec.Vec.new] at transport ⊢
    rw [transport]
    exact loop_malformed_next file env frame values tail a b c d rest maxRecords _ separate bounded more (by omega) bad _ next
  · exact ⟨bound, Nat.le_refl _, offset⟩
  · simp [blocked, outcome]
  · simpa [planned, sought] using seek_start
      (⟨data, data, position, outcome "seek" true 0 (zeroMask data) (planned data rest stop 0).script⟩ : State)
      0#u64 (zeroMask data) data _ (by simp [limit]) (action_outcome _ _ _ _ _) (persist_zero _)

@[expose] def malformedRepaired (values : List U16) (rest : Term) : State :=
  ⟨disk (logBytes values), disk (logBytes values), 4 * values.length + 4, rest⟩

/-- Actual Rust repair removes the first invalid record and all later bytes,
then acknowledges only after synchronization. The file offset records exactly
the bytes inspected, rather than pretending the unread suffix was consumed. -/
theorem repair_malformed (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8) (a b c d : U8)
    (mask durable syncMask : ByteArray) (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame)
    (bounded : (logBytes values ++ suffixBytes a b c d tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX)
    (accepted : persist (disk (logBytes values ++ suffixBytes a b c d tail))
      (disk (logBytes values)) mask = some durable) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ suffixBytes a b c d tail), disk (logBytes values ++ suffixBytes a b c d tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ suffixBytes a b c d tail)))
          (planned (disk (logBytes values ++ suffixBytes a b c d tail))
            (outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest)) (4 * values.length + 4) 0).script⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (malformedRepaired values rest) frame) := by
  let data := disk (logBytes values ++ suffixBytes a b c d tail)
  let plan := outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest)
  have capacity : values.length < 262144 := by
    simp only [List.length_append, logBytes_length, suffixBytes, List.length_cons, List.length_nil, limit] at bounded
    omega
  have size : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  simp only [repair_log, monadLift_self]
  rw [recover_malformed_next file env frame values tail a b c d plan position maxRecords separate bounded offset more bad]
  have unequal : (alloc.vec.Vec.from values (by scalar_tac)).len ≠ maxRecords := by
    intro equality
    have := congrArg UScalar.val equality
    simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, Usize.ofNatCore, UScalar.ofNatCore_val_eq] at this
    omega
  simp only [NativeM.ok, Result.ok_bind]
  rw [ite_eq_right unequal]
  simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, NativeM.lift]
  have cast : UScalar.cast .U64 (Usize.ofNatCore values.length (by scalar_tac)) =
      U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega) := by
    apply UScalar.eq_of_val_eq
    have small : values.length < 18446744073709551616 := by omega
    simp [UScalar.cast_val_eq, Usize.ofNatCore, U64.ofNatCore]
    omega
  rw [cast]
  simp only [Result.ok_bind]
  have multiply : U64.checked_mul (U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega)) 4#u64 =
      some (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega)) := by
    apply NativeM.checkedMulU64_of_val
    simp [U64.ofNatCore, Nat.mul_comm]
  rw [multiply]
  simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
  have resizedBytes : resize data (4 * values.length) = disk (logBytes values) := by
    simpa only [logBytes_length] using resize_prefix (logBytes values) (suffixBytes a b c d tail)
  have positionBound : 4 * values.length + 4 ≤ limit := by
    simp only [limit]
    omega
  simp only [planned, Nat.sub_self, readScript]
  rw [resize_success_next file (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega)) env frame
    (⟨data, data, 4 * values.length + 4, plan⟩ : State) mask durable syncMask rest separate]
  · simp [resized, malformedRepaired, resizedBytes, U64.ofNatCore, data]
  · exact ⟨size, size, positionBound⟩
  · simp [U64.ofNatCore, limit]; omega
  · rfl
  · simpa [U64.ofNatCore, resizedBytes] using accepted

/-- Successful repair is witnessed by a concrete admitted script for every
invalid record and arbitrary following bytes, without assumed persistence equations. -/
theorem repair_malformed_default (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8) (a b c d : U8)
    (rest : Term) (position : Nat) (maxRecords : Usize) (separate : Separate file frame)
    (bounded : (logBytes values ++ suffixBytes a b c d tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ suffixBytes a b c d tail), disk (logBytes values ++ suffixBytes a b c d tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ suffixBytes a b c d tail)))
          (planned (disk (logBytes values ++ suffixBytes a b c d tail))
            (outcome "set_len" true 0 (zeroMask (disk (logBytes values ++ suffixBytes a b c d tail)))
              (outcome "sync_all" true 0 ByteArray.empty rest)) (4 * values.length + 4) 0).script⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (malformedRepaired values rest) frame) := by
  exact repair_malformed file env frame values tail a b c d _ _ ByteArray.empty rest position maxRecords
    separate bounded offset more bad (persist_keep_old _ _)

/-- The standalone actual recovery result retains the full file and stops at
the first rejected record, without reading or accepting later records. -/
theorem recover_malformed (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8) (a b c d : U8)
    (rest : Term) (position : Nat) (maxRecords : Usize) (separate : Separate file frame)
    (bounded : (logBytes values ++ suffixBytes a b c d tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX) :
    recover_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ suffixBytes a b c d tail), disk (logBytes values ++ suffixBytes a b c d tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ suffixBytes a b c d tail)))
          (planned (disk (logBytes values ++ suffixBytes a b c d tail)) rest (4 * values.length + 4) 0).script⟩ frame) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        fileEnv env file (planned (disk (logBytes values ++ suffixBytes a b c d tail)) rest
          (4 * values.length + 4) (4 * values.length + 4)) frame) := by
  simpa [NativeM.ok] using recover_malformed_next file env frame values tail a b c d rest position maxRecords
    separate bounded offset more bad (fun result => NativeM.ok result)

/-- Once repair acknowledges success, every admitted crash has exactly the
complete prefix. Fresh actual repair then returns that same prefix again. -/
theorem repair_malformed_crash (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8) (a b c d : U8)
    (mask durable syncMask crashMask : ByteArray) (rest recoveryRest : Term)
    (position : Nat) (maxRecords : Usize) (image : Image) (separate : Separate file frame)
    (bounded : (logBytes values ++ suffixBytes a b c d tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (bad : word a b ^^^ word c d ≠ core.num.U16.MAX)
    (accepted : persist (disk (logBytes values ++ suffixBytes a b c d tail))
      (disk (logBytes values)) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (malformedRepaired values rest) frame) = some image) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ suffixBytes a b c d tail), disk (logBytes values ++ suffixBytes a b c d tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ suffixBytes a b c d tail)))
          (planned (disk (logBytes values ++ suffixBytes a b c d tail))
            (outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest)) (4 * values.length + 4) 0).script⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (malformedRepaired values rest) frame) ∧
    image.bytes = disk (logBytes values) ∧
    repair_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes (outcome "set_len" true 0 (zeroMask image.bytes)
          (outcome "sync_all" true 0 ByteArray.empty recoveryRest)) 0).script)) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨disk (logBytes values), disk (logBytes values), image.bytes.size, recoveryRest⟩ []) := by
  have sizeBound : (disk (logBytes values)).size + 4 ≤ limit := by
    simpa [disk, ← ByteArray.size_data, suffixBytes, List.length_append] using
      (show (logBytes values).length + 4 ≤ limit by
        simp only [List.length_append, suffixBytes, List.length_cons, List.length_nil] at bounded
        omega)
  have positionBound : 4 * values.length + 4 ≤ limit := by simpa [disk, ← ByteArray.size_data] using sizeBound
  have valid : Valid (malformedRepaired values rest) := by
    change (disk (logBytes values)).size ≤ limit ∧ (disk (logBytes values)).size ≤ (disk (logBytes values)).size ∧
      4 * values.length + 4 ≤ limit
    exact ⟨by omega, Nat.le_refl _, positionBound⟩
  have stable := stable_image file env frame _ crashMask image separate valid rfl captured
  have shape : image.bytes = disk (logBytes values) := by simpa only [malformedRepaired] using stable.1
  refine ⟨repair_malformed file env frame values tail a b c d mask durable syncMask rest position maxRecords
    separate bounded offset more bad accepted, shape, ?_⟩
  apply restart_repair values image recoveryRest maxRecords
  · rw [shape]
    simpa only [List.append_nil] using log_image values [] (by simp)
  · rw [shape]
    omega
  · exact more

end Record.MalformedProperties
