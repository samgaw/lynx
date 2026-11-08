module
public import Record.CrashProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.AppendProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties

/-- Exhausting a continuing loop never fabricates a successful return. -/
theorem continuing_cutoff (fuel : Nat) (state : α) :
    NativeM.loopFuel (fun x => NativeM.ok (Aeneas.Std.ControlFlow.cont x : Aeneas.Std.ControlFlow α β))
      fuel state = Result.error .exhausted := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa [NativeM.loopFuel, NativeM.ok] using ih

/-- Record parsing composes through an actual loop continuation. -/
theorem record_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (s0 s1 s2 s3 s4 : State) (value : U16)
    (separate : Separate file frame)
    (v0 : Valid s0) (v1 : Valid s1) (v2 : Valid s2) (v3 : Valid s3)
    (n0 : blocked s0 = false) (n1 : blocked s1 = false)
    (n2 : blocked s2 = false) (n3 : blocked s3 = false)
    (r0 : readStep s0 (one 0#u8) = some (.Ok 1#usize, s1, one (low value)))
    (r1 : readStep s1 (one 0#u8) = some (.Ok 1#usize, s2, one (high value)))
    (r2 : readStep s2 (one 0#u8) = some (.Ok 1#usize, s3, one (low (~~~value))))
    (r3 : readStep s3 (one 0#u8) = some (.Ok 1#usize, s4, one (high (~~~value))))
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next).run (fileEnv env file s0 frame) =
      (next (.Ok (some value), file)).run (fileEnv env file s4 frame) := by
  simp only [read_record, monadLift_self, bind_assoc]
  rw [word_next file env frame s0 s1 s2 _ _ separate v0 v1 n0 n1 r0 r1]
  simp only [bind_assoc]
  rw [word_next file env frame s2 s3 s4 _ _ separate v2 v3 n2 n3 r2 r3]
  simp [decode_layout, NativeM.ok]

@[expose] def pairData (first second : U16) : ByteArray :=
  disk ((layout first).val ++ (layout second).val)

theorem first_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (first second : U16) (rest : Term)
    (separate : Separate file frame)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next).run (fileEnv env file (scanning (pairData first second) rest 0) frame) =
      (next (.Ok (some first), file)).run (fileEnv env file (scanning (pairData first second) rest 4) frame) := by
  apply record_next file env frame _ (scanning (pairData first second) rest 1)
    (scanning (pairData first second) rest 2) (scanning (pairData first second) rest 3)
    (scanning (pairData first second) rest 4) first separate
  all_goals simp [pairData, disk, layout, scanning, eofPlan, Valid, blocked, limit,
    readScript, outcome, readStep, action, persist_zero, one, readBuffer, raw_toNat,
    restore_byte, Usize.ofNatCore, ← ByteArray.size_data]

theorem second_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (first second : U16) (rest : Term)
    (separate : Separate file frame)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next).run (fileEnv env file (scanning (pairData first second) rest 4) frame) =
      (next (.Ok (some second), file)).run (fileEnv env file (scanning (pairData first second) rest 8) frame) := by
  apply record_next file env frame _ (scanning (pairData first second) rest 5)
    (scanning (pairData first second) rest 6) (scanning (pairData first second) rest 7)
    (scanning (pairData first second) rest 8) second separate
  all_goals simp [pairData, disk, layout, scanning, eofPlan, Valid, blocked, limit,
    readScript, outcome, readStep, action, persist_zero, one, readBuffer, raw_toNat,
    restore_byte, Usize.ofNatCore, ← ByteArray.size_data]

theorem push_from (values : List U16) (value : U16) (bound : values.length < 262144)
    (valid : values.length ≤ Usize.max) :
    Record.Extraction.VectorModel.push (alloc.vec.Vec.from values valid) value =
      RustM.ok (alloc.vec.Vec.from (values ++ [value]) (by simp; scalar_tac)) := by
  have capacity : values.length + 1 ≤ U32.max := by scalar_tac
  simp [Record.Extraction.VectorModel.push, alloc.vec.Vec.push, bound, capacity]

/-- The actual loop returns both original payloads in order and advances over
exactly their eight bytes. It does not restart the parser between iterations. -/
theorem recover_log_two (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (first second : U16) (rest : Term) (position : Nat)
    (separate : Separate file frame) (bounded : position ≤ limit) :
    recover_log file 2#usize (fileEnv env file
      ⟨pairData first second, pairData first second, position, recoveryScript (pairData first second) rest⟩ frame) =
      (.ok (.Ok (alloc.vec.Vec.from [first, second] (by scalar_tac)), file),
        fileEnv env file (scanning (pairData first second) rest 8) frame) := by
  simp only [recover_log, monadLift_self]
  rw [seek_next file 0#u64 env frame _ (scanning (pairData first second) rest 0) (.Ok 0#u64) separate]
  · simp only [recover_log_loop, monadLift_self, NativeM.loop]
    rw [NativeM.loopFuel]
    have start : (alloc.vec.Vec.new U16).len < 2#usize := by
      simp [alloc.vec.Vec.len, alloc.vec.Vec.new]
    simp only [recover_log_loop.body, monadLift_self, start, ite_true, bind_assoc]
    change (read_record file >>= _).run _ = _
    rw [first_next file env frame first second rest separate]
    simp only [NativeM.ok, Result.ok_bind]
    rw [push_from [] first (by decide)]
    simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind, List.nil_append, List.cons_append]
    rw [NativeM.loopFuel]
    have again : (alloc.vec.Vec.from [first] (by scalar_tac)).len < 2#usize := by
      simp [alloc.vec.Vec.len]
    simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, List.length_cons, List.length_nil,
      Usize.ofNatCore, UScalar.lt_equiv, UScalar.ofNat, UScalar.ofNatCore_val_eq,
      Nat.reduceAdd, Nat.reduceLT, ite_true, bind_assoc]
    change (read_record file >>= _).run _ = _
    rw [second_next file env frame first second rest separate]
    simp only [NativeM.ok, Result.ok_bind]
    rw [push_from [first] second (by simp)]
    simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind, List.nil_append, List.cons_append]
    rw [NativeM.loopFuel]
    have stop : ¬(alloc.vec.Vec.from [first,second] (by scalar_tac)).len < 2#usize := by
      simp [alloc.vec.Vec.len]
    simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, List.length_cons, List.length_nil,
      Usize.ofNatCore, UScalar.lt_equiv, UScalar.ofNat, UScalar.ofNatCore_val_eq,
      Nat.reduceAdd, Nat.reduceLT, ite_false, NativeM.ok, Result.ok_bind, Result.ok_apply]
  · simpa [Valid, pairData, disk, layout, ← ByteArray.size_data, limit] using bounded
  · simp [blocked, recoveryScript, outcome]
  · simpa [scanning, recoveryScript, sought] using seek_start
      (⟨pairData first second, pairData first second, position, recoveryScript (pairData first second) rest⟩ : State)
      0#u64 (zeroMask (pairData first second)) (pairData first second) _ (by simp [limit])
      (action_outcome _ _ _ _ _) (persist_zero _)


/-- The facade seeks to the current end before it invokes the verified writer. -/
theorem append_ready (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State) (offset : U64)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (step : seekStep before (.end_ 0#i64) = some (.Ok offset, after)) :
    append_record file value (fileEnv env file before frame) =
      write_record file value (fileEnv env file after frame) := by
  have ready : pollSeek file (.end_ 0#i64) (fileEnv env file before frame) =
      some (.ok (.Ok offset, file), fileEnv env file after frame) := by
    simp [pollSeek, lookup_at env file before frame separate valid, notBlocked,
      step, store_at env file before after frame separate]
  simp only [append_record, io_core.seek_from, Record.Extraction.FileModel.seek,
    monadLift_self, NativeFile.seek, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp [Result.ok_bind]

theorem append_bytes (before : ByteArray) (value : U16) :
    (overwrite before before.size (bytes (payload value)) 4).data.toList =
      before.data.toList ++ (encoded value).data.toList := by
  have dropped : before.data.toList.drop (before.size + 4) = [] := by
    apply List.drop_eq_nil_of_le
    simp [← ByteArray.size_data]
  simp [overwrite, payload_bytes, encoded, fourBytes, dropped, ← ByteArray.size_data]

/-- End-relative seek computes the visible length without changing any byte. -/
theorem seek_end_step (before : State) (valid : Valid before) (mask durable : ByteArray) (rest : Term)
    (choice : action "seek" before.script = some (true, 0, mask, rest))
    (accepted : persist before.durable before.visible mask = some durable) :
    seekStep before (.end_ 0#i64) = some
      (.Ok (U64.ofNatCore before.visible.size (by have := valid.1; simp only [limit] at this; scalar_tac)),
        sought before before.visible.size durable rest) := by
  have bound := valid.1
  simp [seekStep, seekTarget, choice, accepted, sought, not_lt.mpr bound]

@[expose] def appended (before : State) (value : U16) (rest : Term) : State :=
  ⟨overwrite before.visible before.visible.size (bytes (payload value)) 4,
    overwrite before.visible before.visible.size (bytes (payload value)) 4,
    before.visible.size + 4, rest⟩

/-- Every prior byte is retained by an acknowledged append, including when the
incoming offset points inside an existing record. -/
theorem append_success (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (mask durable syncMask : ByteArray)
    (rest : Term) (separate : Separate file frame) (valid : Valid before)
    (stable : before.durable = before.visible) (fits : before.visible.size + 4 ≤ limit)
    (script : before.script = outcome "seek" true 0 (zeroMask before.visible)
      (outcome "write" true 4 mask (outcome "sync_all" true 0 syncMask rest)))
    (accepted : persist before.visible
      (overwrite before.visible before.visible.size (bytes (payload value)) 4) mask = some durable) :
    append_record file value (fileEnv env file before frame) =
      (.ok (.Ok true, file), fileEnv env file (appended before value rest) frame) ∧
    (appended before value rest).visible.data.toList =
      before.visible.data.toList ++ (encoded value).data.toList := by
  let after := sought before before.visible.size before.visible
    (outcome "write" true 4 mask (outcome "sync_all" true 0 syncMask rest))
  have step : seekStep before (.end_ 0#i64) = some
      (.Ok (U64.ofNatCore before.visible.size (by have := valid.1; simp only [limit] at this; scalar_tac)), after) := by
    apply seek_end_step before valid (zeroMask before.visible) before.visible _
    · rw [script, action_outcome]
    · rw [stable]
      exact persist_zero before.visible
  constructor
  · rw [append_ready file value env frame before after _ separate valid
      (by simp [blocked, script, outcome]) step]
    simpa [appended, committed, after, sought] using write_record_success file value env frame after
      4 mask durable syncMask rest separate
      (by change before.visible.size ≤ limit ∧ before.visible.size ≤ before.visible.size ∧ before.visible.size ≤ limit
          exact ⟨valid.1, Nat.le_refl before.visible.size, valid.1⟩)
      (by simp [payload, layout]) (by simp [payload, layout, limit])
      (by simpa [after, sought] using fits) rfl accepted
  · exact append_bytes before.visible value


/-- Any post-acknowledgement crash preserves every previously present byte. -/
theorem append_crash_prefix (file : NativeFile) (value : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (mask durable syncMask crashMask : ByteArray)
    (rest : Term) (image : Image) (separate : Separate file frame) (valid : Valid before)
    (stable : before.durable = before.visible) (fits : before.visible.size + 4 ≤ limit)
    (script : before.script = outcome "seek" true 0 (zeroMask before.visible)
      (outcome "write" true 4 mask (outcome "sync_all" true 0 syncMask rest)))
    (accepted : persist before.visible
      (overwrite before.visible before.visible.size (bytes (payload value)) 4) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (appended before value rest) frame) = some image) :
    append_record file value (fileEnv env file before frame) =
      (.ok (.Ok true, file), fileEnv env file (appended before value rest) frame) ∧
    image.bytes.data.toList = before.visible.data.toList ++ (encoded value).data.toList := by
  have proof := append_success file value env frame before mask durable syncMask rest
    separate valid stable fits script accepted
  have afterValid : Valid (appended before value rest) := by
    have size := overwrite_size before.visible (bytes (payload value)) before.visible.size 4
      (by simp [bytes_size, payload, layout])
    have length : (overwrite before.visible before.visible.size (bytes (payload value)) 4).size =
        before.visible.size + 4 := by simpa using size
    simp only [Valid, appended, length]
    exact ⟨fits, Nat.le_refl _, fits⟩
  have persisted := (stable_image file env frame (appended before value rest) crashMask image
    separate afterValid rfl captured).1
  exact ⟨proof.1, by rw [persisted]; exact proof.2⟩

/-- The original acknowledged record and a second acknowledged append both
survive every admitted post-sync crash and the actual multi-record recovery loop. -/
theorem append_pair_recovery (file : NativeFile) (first second : U16) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (mask durable syncMask crashMask : ByteArray)
    (rest recoveryRest : Term) (image : Image) (separate : Separate file frame) (valid : Valid before)
    (initial : before.visible = encoded first) (stable : before.durable = before.visible)
    (script : before.script = outcome "seek" true 0 (zeroMask before.visible)
      (outcome "write" true 4 mask (outcome "sync_all" true 0 syncMask rest)))
    (accepted : persist before.visible
      (overwrite before.visible before.visible.size (bytes (payload second)) 4) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (appended before second rest) frame) = some image) :
    append_record file second (fileEnv env file before frame) =
      (.ok (.Ok true, file), fileEnv env file (appended before second rest) frame) ∧
    recover_log ⟨image.highWater + 1⟩ 2#usize
      (restarted image (recoveryScript image.bytes recoveryRest)) =
      (.ok (.Ok (alloc.vec.Vec.from [first,second] (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ (scanning image.bytes recoveryRest 8) []) := by
  have fits : before.visible.size + 4 ≤ limit := by
    simp [initial, encoded, fourBytes, ← ByteArray.size_data, limit]
  have proof := append_crash_prefix file second env frame before mask durable syncMask crashMask rest
    image separate valid stable fits script accepted captured
  have shape : image.bytes = pairData first second := by
    apply ByteArray.ext
    apply _root_.Array.toList_inj.mp
    simpa [initial, pairData, disk, layout, encoded, fourBytes, rawByte] using proof.2
  refine ⟨proof.1, ?_⟩
  rw [restart_as_fileEnv]
  simpa only [shape] using recover_log_two (⟨image.highWater + 1⟩ : NativeFile) ({} : Environment) []
    first second recoveryRest 0 (by simp [Separate]) (by simp [limit])

end Record.AppendProperties
