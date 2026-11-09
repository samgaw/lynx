module
public import Record.ResizeProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairCrashProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties
  Record.LogProperties Record.TailProperties Record.ResizeProperties

/-- The complete acknowledged prefix is present byte for byte. -/
@[expose] def Prefix (head data : ByteArray) : Prop :=
  head.size ≤ data.size ∧ ∀ i, i < head.size → data[i]! = head[i]!

/-- A crash image may retain some partial-tail bytes, but no complete extra
record. The retained tail bytes need not equal the original partial tail. -/
@[expose] def LogImage (values : List U16) (data : ByteArray) : Prop :=
  Prefix (disk (logBytes values)) data ∧ data.size < (disk (logBytes values)).size + 4

theorem prefix_append (head tail : List U8) : Prefix (disk head) (disk (head ++ tail)) := by
  constructor
  · simp [disk, ← ByteArray.size_data]
  · intro i inside
    have bound : i < head.length := by simpa [disk, ← ByteArray.size_data] using inside
    rw [getElem!_pos (disk (head ++ tail)) i (by simp [disk, ← ByteArray.size_data]; omega),
      getElem!_pos (disk head) i inside]
    simp [disk, ByteArray.getElem_eq_getElem_data, List.getElem_append_left, bound]

theorem log_image (values : List U16) (tail : List U8) (short : tail.length < 4) :
    LogImage values (disk (logBytes values ++ tail)) := by
  exact ⟨prefix_append _ _, by simpa [disk, ← ByteArray.size_data] using short⟩

theorem persist_lengths (old visible mask result : ByteArray)
    (accepted : persist old visible mask = some result) :
    min old.size visible.size ≤ result.size ∧ result.size ≤ max old.size visible.size := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    cases accepted
    simpa [← ByteArray.size_data] using And.intro conditions.1 conditions.2.1
  · contradiction

/-- Every admitted background persistence choice preserves the complete
prefix and the strict partial-tail bound, including repeated choices. -/
theorem persist_log_image (values : List U16) (old visible mask result : ByteArray)
    (oldImage : LogImage values old) (visibleImage : LogImage values visible)
    (accepted : persist old visible mask = some result) : LogImage values result := by
  have sizes := persist_lengths old visible mask result accepted
  refine ⟨⟨by have := oldImage.1.1; have := visibleImage.1.1; omega, ?_⟩,
    by have := oldImage.2; have := visibleImage.2; omega⟩
  intro i inside
  rw [persist_at old visible mask result accepted i (by
    have := oldImage.1.1; have := visibleImage.1.1; omega)]
  split
  · exact visibleImage.1.2 i inside
  · exact oldImage.1.2 i inside

/-- Translate the byte-prefix invariant into the exact input shape needed by
the implementation-linked truncated-log recovery theorem. -/
theorem log_image_shape (values : List U16) (data : ByteArray) (image : LogImage values data) :
    ∃ tail : List U8, tail.length < 4 ∧ data = disk (logBytes values ++ tail) := by
  let head := disk (logBytes values)
  change Prefix head data ∧ data.size < head.size + 4 at image
  have equal : data.data.toList.take head.size = head.data.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, _root_.Array.length_toList, ← ByteArray.size_data]
      exact Nat.min_eq_left image.1.1
    · intro i hi hj
      have inside : i < head.size := by simpa only [_root_.Array.length_toList, ← ByteArray.size_data] using hj
      have bytes := image.1.2 i inside
      rw [getElem!_pos data i (by have bound := image.1.1; omega), getElem!_pos head i inside] at bytes
      simpa only [List.getElem_take, _root_.Array.getElem_toList, ByteArray.getElem_eq_getElem_data] using bytes
  let tail := (data.data.toList.drop head.size).map byteValue
  refine ⟨tail, ?_, ?_⟩
  · simp only [tail, List.length_map, List.length_drop, _root_.Array.length_toList, ← ByteArray.size_data]
    have bound := image.2
    simp only [← ByteArray.size_data] at bound
    omega
  · have reconstruct := List.take_append_drop head.size data.data.toList
    rw [equal] at reconstruct
    have headRoundtrip : head.data.toList.map byteValue = logBytes values := by
      simp [head, disk, List.map_map, Function.comp_def, byte_roundtrip]
    have decoded := congrArg (List.map byteValue) reconstruct
    simp only [List.map_append, headRoundtrip] at decoded
    rw [← disk_roundtrip data, ← decoded]

@[expose] def repairReply (file : NativeFile) (values : alloc.vec.Vec U16) :
    core.result.Result Unit NativeIoError → NativeM
      (core.result.Result (Option (alloc.vec.Vec U16)) NativeIoError × NativeFile)
  | .Ok () => NativeM.ok (.Ok (some values), file)
  | .Err error => NativeM.ok (.Err error, file)

/-- The actual recovery and checked byte-length arithmetic lead to the actual
resize/sync continuation. No successful sync result is required to reach it. -/
theorem repair_prepare (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (plan : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail)) plan 0).script⟩ frame) =
      (resize_then_sync file (U64.ofNatCore (4 * values.length) (by
          have bound := bounded
          simp only [List.length_append, logBytes_length, limit, UScalarTy.numBits] at *
          omega)) >>= repairReply file (alloc.vec.Vec.from values (by scalar_tac))).run
        (fileEnv env file (finished (disk (logBytes values ++ tail)) plan) frame) := by
  let data := disk (logBytes values ++ tail)
  have capacity : values.length ≤ 262144 := by
    simp only [List.length_append, logBytes_length, limit] at bounded
    omega
  simp only [repair_log, monadLift_self]
  rw [recover_truncated_log_next file env frame values tail plan position maxRecords separate short bounded offset more]
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
  apply congrArg (fun continuation =>
    (resize_then_sync file (U64.ofNatCore (4 * values.length) (by simp only [UScalarTy.numBits]; omega))
      >>= continuation) (fileEnv env file (finished data plan) frame))
  funext reply
  cases reply with
  | Ok returned => cases returned; simp [repairReply, NativeM.ok]
  | Err error => simp [repairReply, NativeM.ok]

/-- A completed length change leaves the actual synchronization operation as
the remaining computation, for every admitted persistence outcome. -/
theorem resize_pending (file : NativeFile) (length : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Admitted before) (bounded : length.val ≤ limit)
    (script : before.script = outcome "set_len" true 0 mask rest)
    (accepted : persist before.durable (resize before.visible length.val) mask = some durable)
    (next : core.result.Result Unit NativeIoError → NativeM α) :
    (resize_then_sync file length >>= next).run (fileEnv env file before frame) =
      (io_core.synchronize file >>= next).run (fileEnv env file
        ⟨resize before.visible length.val, durable, before.position, rest⟩ frame) := by
  simp only [resize_then_sync, monadLift_self, bind_assoc]
  rw [resize_next file length env frame before
    ⟨resize before.visible length.val, durable, before.position, rest⟩ (.Ok ()) separate valid
    (by simp [blocked, script, outcome])
    (by simp [setLenStep, script, action_outcome, not_lt.mpr bounded, accepted])]

/-- Any admitted crash preserves the prefix invariant, even when durable and
visible lengths differ and another persistence choice occurs at power loss. -/
theorem crash_log_image (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State) (values : List U16)
    (mask : ByteArray) (image : Image) (separate : Separate file frame)
    (valid : Admitted state) (visible : LogImage values state.visible)
    (durable : LogImage values state.durable)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    LogImage values image.bytes ∧ image.bytes.size ≤ limit := by
  unfold crashImage at captured
  rw [lookup_admitted env file state frame separate valid] at captured
  change (persist state.durable state.visible mask).bind (fun bytes =>
    some (⟨bytes, (fileEnv env file state frame).nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨bytes, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  have lengths := persist_lengths _ _ _ _ accepted
  exact ⟨persist_log_image values _ _ _ _ durable visible accepted,
    by have := valid.1; have := valid.2.1; dsimp; omega⟩

/-- Restart from any retained partial tail admitted by the byte invariant.
The actual Rust recovery returns exactly the acknowledged complete records. -/
theorem crash_retry (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State) (values : List U16)
    (mask : ByteArray) (image : Image) (rest : Term) (maxRecords : Usize)
    (separate : Separate file frame) (valid : Admitted state)
    (visible : LogImage values state.visible) (durable : LogImage values state.durable)
    (more : values.length < maxRecords.val)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    recover_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes rest 0).script)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ (finished image.bytes rest) []) := by
  have shape := crash_log_image file env frame state values mask image separate valid visible durable captured
  obtain ⟨tail, short, contents⟩ := log_image_shape values image.bytes shape.1
  have bound : (logBytes values ++ tail).length ≤ limit := by
    simpa [contents, disk, ← ByteArray.size_data] using shape.2
  rw [restart_as_fileEnv]
  simpa only [contents] using recover_truncated_log (⟨image.highWater + 1⟩ : NativeFile)
    ({} : Environment) [] values tail rest 0 maxRecords (by simp [Separate]) short bound (by simp [limit]) more

@[expose] def pendingRepair (values : List U16) (tail : List U8) (durable : ByteArray) (rest : Term) : State :=
  ⟨disk (logBytes values), durable, (disk (logBytes values ++ tail)).size, rest⟩

/-- Actual recovery, arithmetic and resize lead to the actual sync continuation,
without assuming sync completes or repair is acknowledged. -/
theorem repair_at_sync (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (mask durable : ByteArray) (rest : Term) (position : Nat) (maxRecords : Usize)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (accepted : persist (disk (logBytes values ++ tail)) (disk (logBytes values)) mask = some durable) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail)) (outcome "set_len" true 0 mask rest) 0).script⟩ frame) =
      (io_core.synchronize file >>= repairReply file (alloc.vec.Vec.from values (by scalar_tac))).run
        (fileEnv env file (pendingRepair values tail durable rest) frame) := by
  have capacity : values.length ≤ 262144 := by
    simp only [List.length_append, logBytes_length, limit] at bounded
    omega
  let data := disk (logBytes values ++ tail)
  have bound : data.size ≤ limit := by simpa [data, disk, ← ByteArray.size_data] using bounded
  have lengthBound : 4 * values.length ≤ limit := by simp only [limit]; omega
  have resizedBytes : resize data (4 * values.length) = disk (logBytes values) := by
    simpa only [logBytes_length] using resize_prefix (logBytes values) tail
  rw [repair_prepare file env frame values tail _ position maxRecords separate short bounded offset more]
  rw [resize_pending file _ env frame (finished data (outcome "set_len" true 0 mask rest))
    mask durable rest separate ⟨bound, bound, bound⟩]
  · simp only [pendingRepair, finished, U64.ofNatCore, UScalar.ofNatCore_val_eq, resizedBytes, data]
  · simpa [U64.ofNatCore] using lengthBound
  · rfl
  · simpa [finished, U64.ofNatCore, resizedBytes] using accepted

/-- The state reached after the actual resize retains the complete prefix,
even if the old durable length has not shrunk at all. -/
theorem pending_image (values : List U16) (tail : List U8) (mask durable : ByteArray) (rest : Term)
    (short : tail.length < 4) (bounded : (logBytes values ++ tail).length ≤ limit)
    (accepted : persist (disk (logBytes values ++ tail)) (disk (logBytes values)) mask = some durable) :
    Admitted (pendingRepair values tail durable rest) ∧
    LogImage values (pendingRepair values tail durable rest).visible ∧
    LogImage values (pendingRepair values tail durable rest).durable := by
  have old := log_image values tail short
  have visible : LogImage values (disk (logBytes values)) := by
    simpa only [List.append_nil] using log_image values [] (by simp)
  have kept := persist_log_image values _ _ _ _ old visible accepted
  have lengths := persist_lengths _ _ _ _ accepted
  have bound : (disk (logBytes values ++ tail)).size ≤ limit := by
    simpa [disk, ← ByteArray.size_data] using bounded
  have prefixBound : (disk (logBytes values)).size ≤ limit := by
    have := (prefix_append (logBytes values) tail).1
    omega
  refine ⟨?_, visible, kept⟩
  change (disk (logBytes values)).size ≤ limit ∧ durable.size ≤ limit ∧ (disk (logBytes values ++ tail)).size ≤ limit
  exact ⟨prefixBound, by omega, bound⟩

/-- A fresh call of the actual Rust repair routine succeeds on every image
classified by the prefix invariant, removing whatever partial tail remains. -/
theorem restart_repair (values : List U16) (image : Image) (rest : Term) (maxRecords : Usize)
    (shape : LogImage values image.bytes) (bounded : image.bytes.size ≤ limit)
    (more : values.length < maxRecords.val) :
    repair_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes (outcome "set_len" true 0 (zeroMask image.bytes)
          (outcome "sync_all" true 0 ByteArray.empty rest)) 0).script)) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨disk (logBytes values), disk (logBytes values), image.bytes.size, rest⟩ []) := by
  obtain ⟨tail, short, contents⟩ := log_image_shape values image.bytes shape
  have bound : (logBytes values ++ tail).length ≤ limit := by
    simpa [contents, disk, ← ByteArray.size_data] using bounded
  rw [restart_as_fileEnv]
  simpa only [contents, repaired] using repair_default (⟨image.highWater + 1⟩ : NativeFile)
    ({} : Environment) [] values tail rest 0 maxRecords (by simp [Separate]) short bound (by simp [limit]) more

/-- Interrupt the actual repair at its blocked synchronization boundary.
All admitted truncation and crash persistence choices retain the acknowledged
prefix; fresh actual repair returns that prefix and durably removes the tail. -/
theorem repair_interrupt (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U16) (tail : List U8)
    (mask durable crashMask : ByteArray) (rest recoveryRest : Term)
    (position : Nat) (maxRecords : Usize) (image : Image)
    (separate : Separate file frame) (short : tail.length < 4)
    (bounded : (logBytes values ++ tail).length ≤ limit)
    (offset : position ≤ limit) (more : values.length < maxRecords.val)
    (accepted : persist (disk (logBytes values ++ tail)) (disk (logBytes values)) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file
      (pendingRepair values tail durable (.cons (.atom "blocked") rest)) frame) = some image) :
    repair_log file maxRecords (fileEnv env file
      ⟨disk (logBytes values ++ tail), disk (logBytes values ++ tail), position,
        outcome "seek" true 0 (zeroMask (disk (logBytes values ++ tail)))
          (reader (disk (logBytes values ++ tail))
            (outcome "set_len" true 0 mask (.cons (.atom "blocked") rest)) 0).script⟩ frame) =
      (io_core.synchronize file >>= repairReply file (alloc.vec.Vec.from values (by scalar_tac))).run
        (fileEnv env file (pendingRepair values tail durable (.cons (.atom "blocked") rest)) frame) ∧
    pollSync file (fileEnv env file (pendingRepair values tail durable (.cons (.atom "blocked") rest)) frame) = none ∧
    repair_log ⟨image.highWater + 1⟩ maxRecords
      (restarted image (outcome "seek" true 0 (zeroMask image.bytes)
        (reader image.bytes (outcome "set_len" true 0 (zeroMask image.bytes)
          (outcome "sync_all" true 0 ByteArray.empty recoveryRest)) 0).script)) =
      (.ok (.Ok (some (alloc.vec.Vec.from values (by scalar_tac))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨disk (logBytes values), disk (logBytes values), image.bytes.size, recoveryRest⟩ []) := by
  have state := pending_image values tail mask durable (.cons (.atom "blocked") rest) short bounded accepted
  have crash := crash_log_image file env frame _ values crashMask image separate state.1 state.2.1 state.2.2 captured
  refine ⟨repair_at_sync file env frame values tail mask durable _ position maxRecords
    separate short bounded offset more accepted, ?_, restart_repair values image recoveryRest maxRecords crash.1 crash.2 more⟩
  simp only [pollSync]
  rw [lookup_admitted env file (pendingRepair values tail durable (.cons (.atom "blocked") rest)) frame separate state.1]
  rfl

end Record.RepairCrashProperties
