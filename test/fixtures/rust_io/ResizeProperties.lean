module
public import Record.TailProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.ResizeProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties

/-- Runtime admission permits an unsynchronized shrink to retain a longer
previous durable image. The growth-only fixture predicate remains stronger. -/
@[expose] def Admitted (state : State) : Prop :=
  state.visible.size ≤ limit ∧ state.durable.size ≤ limit ∧ state.position ≤ limit

theorem decode_admitted (state : State) (valid : Admitted state) :
    decode (encode state) = some state := by
  obtain ⟨visible, durable, position⟩ := valid
  simp [decode, encode, not_lt.mpr visible, not_lt.mpr durable, not_lt.mpr position]

theorem lookup_admitted (env : Environment) (file : NativeFile) (state : State)
    (frame : List (Nat × String × Term)) (separate : Separate file frame) (valid : Admitted state) :
    lookup file (fileEnv env file state frame) = some state := by
  have filtered : frame.filter (fun cell => cell.1 == file.id) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro cell member
    simpa using separate cell member
  simp [lookup, fileEnv, filtered, decode_admitted state valid]

theorem resize_size (data : ByteArray) (length : Nat) : (resize data length).size = length := by
  simp [resize, ← ByteArray.size_data]
  omega

/-- Both old and new lengths remain admitted before synchronization. -/
theorem resize_admitted (before : State) (length : U64) (mask durable : ByteArray) (rest : Term)
    (valid : Admitted before) (bounded : length.val ≤ limit)
    (accepted : persist before.durable (resize before.visible length.val) mask = some durable) :
    Admitted ⟨resize before.visible length.val, durable, before.position, rest⟩ := by
  have sizes := persist_size _ _ _ _ accepted
  rw [resize_size] at sizes
  simp only [Admitted, resize_size]
  exact ⟨bounded, by have := valid.2.1; omega, valid.2.2⟩

theorem resize_next (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (reply : core.result.Result Unit NativeIoError)
    (separate : Separate file frame) (valid : Admitted before)
    (ready : blocked before = false) (step : setLenStep before length = some (reply, after))
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (io_core.resize_to file length >>= next) (fileEnv env file before frame) =
      next reply (fileEnv env file after frame) := by
  have readyPoll : pollSetLen file length (fileEnv env file before frame) =
      some (.ok reply, fileEnv env file after frame) := by
    simp [-getHandle, pollSetLen, no_shared_handle_at env file before frame separate,
      lookup_admitted env file before frame separate valid, ready,
      step, store_at env file before after frame separate]
  simp only [io_core.resize_to, setLen, monadLift_self, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ readyPoll]
  simp [Result.ok_bind]

theorem sync_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (reply : core.result.Result Unit NativeIoError)
    (separate : Separate file frame) (valid : Admitted before)
    (ready : blocked before = false) (step : syncStep before = some (reply, after))
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (io_core.synchronize file >>= next) (fileEnv env file before frame) =
      next reply (fileEnv env file after frame) := by
  have readyPoll : pollSync file (fileEnv env file before frame) =
      some (.ok reply, fileEnv env file after frame) := by
    simp [pollSync, lookup_admitted env file before frame separate valid, ready,
      step, store_at env file before after frame separate]
  simp only [io_core.synchronize, syncAll, monadLift_self, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ readyPoll]
  simp [Result.ok_bind]

@[expose] def resized (before : State) (length : Nat) (rest : Term) : State :=
  ⟨resize before.visible length, resize before.visible length, before.position, rest⟩

/-- The actual two-crate caller acknowledges the new length only after sync.
The offset is preserved even when it lies beyond the new EOF. -/
theorem resize_success_next (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (mask durable syncMask : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Admitted before) (bounded : length.val ≤ limit)
    (script : before.script = outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable (resize before.visible length.val) mask = some durable)
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (resize_then_sync file length >>= next) (fileEnv env file before frame) =
      next (.Ok ()) (fileEnv env file (resized before length.val rest) frame) := by
  let middle : State := ⟨resize before.visible length.val, durable, before.position,
    outcome "sync_all" true 0 syncMask rest⟩
  have step : setLenStep before length = some (.Ok (), middle) := by
    simp [setLenStep, script, action_outcome, not_lt.mpr bounded, accepted, middle]
  simp only [resize_then_sync, monadLift_self, bind_assoc]
  rw [resize_next file length env frame before middle (.Ok ()) separate valid
    (by simp [blocked, script, outcome]) step]
  have sync := sync_next file env frame middle (resized before length.val rest) (.Ok ())
    separate (resize_admitted before length mask durable _ valid bounded accepted)
    (by simp [middle, blocked, outcome]) (by simp [syncStep, middle, action_outcome, resized])
    next
  exact sync

/-- Resizing to the complete prefix removes exactly the tail bytes. -/
theorem resize_prefix (head tail : List U8) :
    resize (disk (head ++ tail)) head.length = disk head := by
  simp [resize, disk, ← ByteArray.size_data, List.map_append]

@[expose] def repaired (values : List U16) (tail : List U8) (rest : Term) : State :=
  ⟨disk (logBytes values), disk (logBytes values), (disk (logBytes values ++ tail)).size, rest⟩

/-- The actual Rust recovery and repair caller retains every complete record,
truncates exactly the rejected suffix and synchronizes before acknowledgement. -/
theorem repair_success (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (mask durable syncMask : ByteArray) (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (accepted : persist (disk (logBytes values ++ tail)) (disk (logBytes values)) mask = some durable) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail))
            (outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest)) 0).script⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (repaired values tail rest) frame) := by
  let data := disk (logBytes values ++ tail)
  let plan := outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest)
  have capacity : values.length ≤ 262144 := by
    simp only [List.length_append, logBytes_length, limit] at bounded
    omega
  have size : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  simp only [repair_log, monadLift_self, bind_assoc]
  rw [recover_truncated_log_next file env frame values tail plan position maxRecords separate short bounded offset more]
  have unequal : (alloc.vec.Vec.from values (by scalar_tac)).len ≠ maxRecords := by
    intro equality
    have := congrArg UScalar.val equality
    simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, Usize.ofNatCore, UScalar.ofNatCore_val_eq] at this
    omega
  simp only [NativeM.ok, Result.ok_bind]
  rw [if_neg unequal]
  simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, NativeM.lift]
  have cast : UScalar.cast .U64 (Usize.ofNatCore values.length (by scalar_tac)) =
      U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega) := by
    apply UScalar.eq_of_val_eq
    have small : values.length < 18446744073709551616 := by omega
    simp [UScalar.cast_val_eq, Usize.ofNatCore, U64.ofNatCore]
    omega
  rw [cast]
  simp only [Result.ok_bind]
  have multiply : (U64.ofNatCore values.length (by simp only [UScalarTy.numBits]; omega) * 4#u64 : RustM U64) =
      RustM.ok (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega)) := by
    have productBound : 4 * values.length < 18446744073709551616 := by omega
    change UScalar.mul _ _ = _
    simp [UScalar.mul, UScalar.tryMk, UScalar.tryMkOpt, UScalar.check_bounds,
      U64.ofNatCore, productBound, RustM.ofOption, Nat.mul_comm]
  rw [multiply]
  simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind, bind_assoc]
  have resizedBytes : resize data (4 * values.length) = disk (logBytes values) := by
    simpa only [logBytes_length] using resize_prefix (logBytes values) tail
  rw [resize_success_next file (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega)) env frame
    (finished data plan) mask durable syncMask rest separate]
  · simp [NativeM.ok, resized, repaired, finished, resizedBytes, U64.ofNatCore, data]
  · exact ⟨size, size, size⟩
  · simp [U64.ofNatCore, limit]; omega
  · rfl
  · simpa [finished, U64.ofNatCore, resizedBytes] using accepted

/-- A failed length change is propagated without attempting synchronization. -/
theorem resize_failure (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (identity : Nat) (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Admitted before) (bounded : length.val ≤ limit)
    (script : before.script = outcome "set_len" false identity mask rest)
    (accepted : persist before.durable before.visible mask = some durable) :
    resize_then_sync file length (fileEnv env file before frame) =
      (.ok (.Err ⟨identity⟩), fileEnv env file {before with durable := durable, script := rest} frame) := by
  simp only [resize_then_sync, monadLift_self]
  rw [resize_next file length env frame before {before with durable := durable, script := rest} (.Err ⟨identity⟩) separate valid
    (by simp [blocked, script, outcome])
    (by simp [setLenStep, script, not_lt.mpr bounded, action_outcome, accepted])]
  simp [NativeM.ok]

/-- Reaching the limit never truncates an unexamined suffix, even when that
suffix contains further complete records. -/
theorem repair_limit (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (count : maxRecords.val = values.length) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail)) rest 0).script⟩ frame) =
      (.ok (.Ok none, file), fileEnv env file
        (reader (disk (logBytes values ++ tail)) rest (4 * values.length)) frame) := by
  let data := disk (logBytes values ++ tail)
  have size : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  have capacity : values.length ≤ 262144 := by
    simp only [List.length_append, logBytes_length, limit] at bounded
    omega
  simp only [repair_log, recover_log, monadLift_self, bind_assoc]
  rw [seek_next file 0#u64 env frame _ (reader data rest 0) (.Ok 0#u64) separate]
  · simp only [recover_log_loop, monadLift_self, NativeM.loop, bind_assoc]
    have trace : Records (reader data rest 0) values (reader data rest (4 * values.length)) := by
      simpa only [List.nil_append, List.length_nil, Nat.zero_add] using reader_records values [] tail rest bounded
    have transport := loop_prefix_next (α := core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile) file env frame _ _ values trace [] maxRecords 262145
      separate (by simp; omega) (by simp; omega) (by omega) (by simp)
    simp only [List.nil_append, alloc.vec.Vec.new] at transport ⊢
    rw [transport]
    obtain ⟨fuel, fuelEq⟩ : ∃ fuel, 262145 - values.length = fuel + 1 := by
      exact ⟨262144 - values.length, by omega⟩
    rw [fuelEq, NativeM.loopFuel]
    have equal : (alloc.vec.Vec.from values (by scalar_tac)).len = maxRecords := by
      apply UScalar.eq_of_val_eq
      simpa [alloc.vec.Vec.len, Usize.ofNatCore] using count.symm
    have stop : ¬(alloc.vec.Vec.from values (by scalar_tac)).len < maxRecords := by
      rw [equal]; exact lt_irrefl _
    simp only [recover_log_loop.body, monadLift_self, stop, ite_false, NativeM.ok,
      Result.ok_bind, equal, ite_true, Result.ok_apply]
    have canonical : Usize.ofNatCore values.length (by scalar_tac) = maxRecords := by
      simpa only [alloc.vec.Vec.len, alloc.vec.Vec.from_val] using equal
    simp [canonical, data]
  · exact ⟨size, Nat.le_refl _, offset⟩
  · simp [blocked, outcome]
  · simpa [reader, sought] using seek_start
      (⟨data, data, position, outcome "seek" true 0 (zeroMask data) (reader data rest 0).script⟩ : State)
      0#u64 (zeroMask data) data _ (by simp [limit]) (action_outcome _ _ _ _ _) (persist_zero _)

/-- Every admitted crash after acknowledged repair contains exactly the
complete prefix. A fresh invocation of actual recovery returns those records. -/
theorem repair_crash (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (mask durable syncMask crashMask : ByteArray) (rest recoveryRest : Term)
    (position : Nat) (maxRecords : Usize) (image : Image)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (accepted : persist (disk (logBytes values ++ tail)) (disk (logBytes values)) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (repaired values tail rest) frame) = some image) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail))
            (outcome "set_len" true 0 mask (outcome "sync_all" true 0 syncMask rest)) 0).script⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (repaired values tail rest) frame) ∧
    image.bytes = disk (logBytes values) ∧
    recover_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes recoveryRest 0).script)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ (finished image.bytes recoveryRest) []) := by
  have bound : (disk (logBytes values ++ tail)).size ≤ limit := by
    simpa [disk, ← ByteArray.size_data] using bounded
  have prefixBound : (disk (logBytes values)).size ≤ limit := by
    simp [disk, ← ByteArray.size_data] at bound ⊢
    omega
  have valid : Valid (repaired values tail rest) := ⟨prefixBound, Nat.le_refl _, bound⟩
  refine ⟨repair_success file env frame values tail mask durable syncMask rest position maxRecords
    separate short bounded offset more accepted, ?_, ?_⟩
  · exact (stable_image file env frame _ crashMask image separate valid rfl captured).1
  · apply restart_truncated_log file env frame _ values [] crashMask image recoveryRest maxRecords
      separate valid rfl (by simp [repaired]) (by simp) more captured

/-- An unsynchronized length change may leave every old durable byte and the
old length. This concrete kernel-checked witness prevents treating set_len as sync. -/
theorem unsynced_shrink (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (rest : Term) (separate : Separate file frame) :
    io_core.resize_to file 2#u64
      (fileEnv env file ⟨disk [1#u8,2#u8,3#u8], disk [1#u8,2#u8,3#u8], 3,
        outcome "set_len" true 0 (zeroMask (disk [1#u8,2#u8,3#u8])) rest⟩ frame) =
      (.ok (.Ok ()), fileEnv env file ⟨disk [1#u8,2#u8], disk [1#u8,2#u8,3#u8], 3, rest⟩ frame) := by
  have transition : setLenStep
      ⟨disk [1#u8,2#u8,3#u8], disk [1#u8,2#u8,3#u8], 3,
        outcome "set_len" true 0 (zeroMask (disk [1#u8,2#u8,3#u8])) rest⟩ 2#u64 =
      some (.Ok (), ⟨disk [1#u8,2#u8], disk [1#u8,2#u8,3#u8], 3, rest⟩) := by
    have lengthChanged : resize (disk [1#u8,2#u8,3#u8]) 2 = disk [1#u8,2#u8] := by decide
    have persistence : persist (disk [1#u8,2#u8,3#u8]) (disk [1#u8,2#u8])
        (zeroMask (disk [1#u8,2#u8,3#u8])) = some (disk [1#u8,2#u8,3#u8]) := by decide
    simp [setLenStep, action_outcome, limit, lengthChanged, persistence]
  simpa [NativeM.ok] using resize_next file 2#u64 env frame _ _ (.Ok ()) separate
    (by simp [Admitted, disk, ← ByteArray.size_data, limit])
    (by simp [blocked, outcome]) transition (fun reply => NativeM.ok reply)

/-- Every old durable byte and its length may remain before sync after shrink. -/
theorem persist_keep_old (old visible : ByteArray) :
    persist old visible (zeroMask old) = some old := by
  have conditions : min old.size visible.size ≤ (zeroMask old).size ∧
      (zeroMask old).size ≤ max old.size visible.size ∧
      ((zeroMask old).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [zeroMask, ← ByteArray.size_data]
  unfold persist
  rw [if_pos conditions]
  congr 1
  apply ByteArray.ext
  apply _root_.Array.ext
  · simp [zeroMask]
  · intro i hi hj
    have inside : i < old.size := by simpa only [ByteArray.size_data] using hj
    simp [zeroMask, getElem!_pos, inside]
    rfl

/-- A concrete admitted resize/sync script proves repair without requiring a
caller-supplied persistence equation. -/
theorem repair_default (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail))
            (outcome "set_len" true 0 (zeroMask (disk (logBytes values ++ tail)))
              (outcome "sync_all" true 0 ByteArray.empty rest)) 0).script⟩ frame) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), file),
        fileEnv env file (repaired values tail rest) frame) := by
  apply repair_success file env frame values tail _ _ ByteArray.empty rest position maxRecords
    separate short bounded offset more
  exact persist_keep_old _ _

/-- A sync error after resize is still an error, even if some new length or
bytes have already persisted. No successful repair acknowledgement is produced. -/
theorem resize_sync_failure (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (mask durable failureMask durableAfter : ByteArray) (identity : Nat) (rest : Term)
    (separate : Separate file frame) (valid : Admitted before) (bounded : length.val ≤ limit)
    (script : before.script = outcome "set_len" true 0 mask (outcome "sync_all" false identity failureMask rest))
    (accepted : persist before.durable (resize before.visible length.val) mask = some durable)
    (failed : persist durable (resize before.visible length.val) failureMask = some durableAfter) :
    resize_then_sync file length (fileEnv env file before frame) =
      (.ok (.Err ⟨identity⟩), fileEnv env file
        ⟨resize before.visible length.val, durableAfter, before.position, rest⟩ frame) := by
  let middle : State := ⟨resize before.visible length.val, durable, before.position,
    outcome "sync_all" false identity failureMask rest⟩
  simp only [resize_then_sync, monadLift_self]
  rw [resize_next file length env frame before middle (.Ok ()) separate valid
    (by simp [blocked, script, outcome])
    (by simp [setLenStep, script, not_lt.mpr bounded, action_outcome, accepted, middle])]
  simpa [NativeM.ok] using sync_next file env frame middle
    ⟨resize before.visible length.val, durableAfter, before.position, rest⟩ (.Err ⟨identity⟩)
    separate (resize_admitted before length mask durable _ valid bounded accepted)
    (by simp [middle, blocked, outcome]) (by simp [syncStep, middle, action_outcome, failed])
    (fun reply => NativeM.ok reply)

/-- A length outside the declared bound is verification exhaustion, not success
or a fabricated Rust I/O error. -/
theorem resize_outside (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (separate : Separate file frame) (valid : Admitted before) (ready : blocked before = false) :
    io_core.resize_to file 1048577#u64 (fileEnv env file before frame) =
      (.error .exhausted, fileEnv env file before frame) := by
  have poll : pollSetLen file 1048577#u64 (fileEnv env file before frame) =
      some (.error .exhausted, fileEnv env file before frame) := by
    simp [-getHandle, pollSetLen, no_shared_handle_at env file before frame separate,
      lookup_admitted env file before frame separate valid, ready, setLenStep, limit]
  simp only [io_core.resize_to, setLen, monadLift_self]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp

end Record.ResizeProperties
