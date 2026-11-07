module
public import Record.IntegrityProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.CrashProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties

@[expose] def crop (data : ByteArray) (length : Nat) : ByteArray :=
  ⟨data.data.extract 0 length⟩

/-- EOF in the first byte composes with the actual caller continuation. -/
theorem word_first_eof_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (first : readStep before (one 0#u8) = some (.Ok 0#usize, after, one 0#u8))
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_word file >>= next) (fileEnv env file before frame) =
      next (.Ok none, file) (fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    bind_assoc, Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before after _ _ separate valid notBlocked first]
  simp [NativeM.ok]

/-- EOF in the second byte never accepts the initialized zero buffer. -/
theorem word_second_eof_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before middle after : State) (lo : U8)
    (separate : Separate file frame) (valid : Valid before) (validMiddle : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one lo))
    (second : readStep middle (one 0#u8) = some (.Ok 0#usize, after, one 0#u8))
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_word file >>= next) (fileEnv env file before frame) =
      next (.Ok none, file) (fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    bind_assoc, Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before middle _ _ separate valid notBlocked first]
  simp only [UScalar.ofNatCore_val_eq, bind_assoc]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame middle after _ _ separate validMiddle notBlockedMiddle second]
  simp [NativeM.ok]

@[expose] def disk (values : List U8) : ByteArray := ⟨(values.map rawByte).toArray⟩
@[expose] def eofPlan (data : ByteArray) (rest : Term) : Term :=
  if data.size < 4 then outcome "read" true 0 (zeroMask data) rest else rest
@[expose] def scanning (data : ByteArray) (rest : Term) (position : Nat) : State :=
  ⟨data, data, position, readScript (zeroMask data) (eofPlan data rest) (data.size - position)⟩
@[expose] def finished (data : ByteArray) (rest : Term) : State :=
  ⟨data, data, data.size, rest⟩

/-- Every byte value is permitted; the bound is the actual truncated length. -/
theorem truncated_reads (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (values : List U8) (rest : Term)
    (separate : Separate file frame) (short : values.length < 4) :
    read_record file (fileEnv env file (scanning (disk values) rest 0) frame) =
      (.ok (.Ok none, file), fileEnv env file (finished (disk values) rest) frame) := by
  cases values with
  | nil =>
    simp only [read_record, monadLift_self]
    rw [word_first_eof_next file env frame _ (finished (disk []) rest) separate]
    · simp [NativeM.ok]
    all_goals simp [scanning, finished, disk, eofPlan, Valid, limit, blocked,
      readScript, outcome, readStep, action, persist_zero, one, readBuffer,
      raw_toNat, restore_byte, Usize.ofNatCore, ← ByteArray.size_data]
  | cons a tail =>
    cases tail with
    | nil =>
      simp only [read_record, monadLift_self]
      rw [word_second_eof_next file env frame _ (scanning (disk [a]) rest 1)
        (finished (disk [a]) rest) a separate]
      · simp [NativeM.ok]
      all_goals simp [scanning, finished, disk, eofPlan, Valid, limit, blocked,
        readScript, outcome, readStep, action, persist_zero, one, readBuffer,
        raw_toNat, restore_byte, Usize.ofNatCore, ← ByteArray.size_data]
    | cons b tail =>
      cases tail with
      | nil =>
        simp only [read_record, monadLift_self]
        rw [word_next file env frame _ (scanning (disk [a,b]) rest 1)
          (scanning (disk [a,b]) rest 2) a b separate]
        · rw [word_first_eof_next file env frame _ (finished (disk [a,b]) rest) separate]
          · simp [NativeM.ok]
          all_goals simp [scanning, finished, disk, eofPlan, Valid, limit, blocked,
            readScript, outcome, readStep, action, persist_zero, one, readBuffer,
            raw_toNat, restore_byte, Usize.ofNatCore, ← ByteArray.size_data]
        all_goals simp [scanning, finished, disk, eofPlan, Valid, limit, blocked,
          readScript, outcome, readStep, action, persist_zero, one, readBuffer,
          raw_toNat, restore_byte, Usize.ofNatCore, ← ByteArray.size_data]
      | cons c tail =>
        cases tail with
        | nil =>
          simp only [read_record, monadLift_self]
          rw [word_next file env frame _ (scanning (disk [a,b,c]) rest 1)
            (scanning (disk [a,b,c]) rest 2) a b separate]
          · rw [word_second_eof_next file env frame _ (scanning (disk [a,b,c]) rest 3)
              (finished (disk [a,b,c]) rest) c separate]
            · simp [NativeM.ok]
            all_goals simp [scanning, finished, disk, eofPlan, Valid, limit, blocked,
              readScript, outcome, readStep, action, persist_zero, one, readBuffer,
              raw_toNat, restore_byte, Usize.ofNatCore, ← ByteArray.size_data]
          all_goals simp [scanning, finished, disk, eofPlan, Valid, limit, blocked,
            readScript, outcome, readStep, action, persist_zero, one, readBuffer,
            raw_toNat, restore_byte, Usize.ofNatCore, ← ByteArray.size_data]
        | cons d tail => simp only [List.length_cons] at short; omega

theorem disk_roundtrip (data : ByteArray) : disk (data.data.toList.map byteValue) = data := by
  apply ByteArray.ext
  apply _root_.Array.ext
  · simp [disk]
  · intro i hi hj
    simp [disk, rawByte, byteValue]

/-- Truncation rejection applies to every byte array, including zero and
nonzero torn bytes. This is a property of the actual extracted record reader. -/
theorem truncated_data (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (data : ByteArray) (rest : Term)
    (separate : Separate file frame) (short : data.size < 4) :
    read_record file (fileEnv env file (scanning data rest 0) frame) =
      (.ok (.Ok none, file), fileEnv env file (finished data rest) frame) := by
  simpa only [disk_roundtrip] using truncated_reads file env frame
    (data.data.toList.map byteValue) rest separate
    (by simpa only [List.length_map, _root_.Array.length_toList, ByteArray.size_data] using short)

@[expose] def recoveryScript (data : ByteArray) (rest : Term) : Term :=
  outcome "seek" true 0 (zeroMask data) (scanning data rest 0).script

/-- The actual recovery seeks to the beginning of every truncated image and
rejects it, regardless of the incoming valid offset. -/
theorem recover_truncated (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (data : ByteArray) (rest : Term) (position : Nat)
    (separate : Separate file frame) (short : data.size < 4) (bounded : position ≤ limit) :
    recover_record file (fileEnv env file
      ⟨data, data, position, recoveryScript data rest⟩ frame) =
      (.ok (.Ok none, file), fileEnv env file (finished data rest) frame) := by
  simp only [recover_record, monadLift_self]
  rw [seek_next file 0#u64 env frame _ (scanning data rest 0) (.Ok 0#u64) separate]
  · exact truncated_data file env frame data rest separate short
  · unfold Valid
    exact ⟨by simp only [limit]; omega, Nat.le_refl _, bounded⟩
  · simp [blocked, recoveryScript, outcome]
  · simpa [scanning, recoveryScript, sought] using seek_start
      (⟨data, data, position, recoveryScript data rest⟩ : State) 0#u64
      (zeroMask data) data (scanning data rest 0).script (by simp [limit])
      (action_outcome _ _ _ _ _) (persist_zero data)

/-- Classify every admitted fresh-slot image, including all shorter lengths.
The choices are derived from the actual persistence mask, not supplied as a
separate assumption about the recovered record. -/
theorem fresh_prefix (value : U16) (mask result : ByteArray)
    (accepted : persist ByteArray.empty
      (fourBytes (low value) (high value) (low (~~~value)) (high (~~~value))) mask = some result) :
    mask.size ≤ 4 ∧ result = crop
      (tornBytes value (mask[0]! == 1) (mask[1]! == 1) (mask[2]! == 1) (mask[3]! == 1)) mask.size := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    have bounded : mask.size ≤ 4 := by
      simpa [fourBytes, ← ByteArray.size_data] using conditions.2.1
    refine ⟨bounded, ?_⟩
    cases accepted
    apply ByteArray.ext
    apply _root_.Array.ext
    · simpa [crop, tornBytes, fourBytes, ← ByteArray.size_data] using bounded
    · intro i hi hj
      have range : i < 4 := by
        have : i < mask.size := by simpa [← ByteArray.size_data] using hi
        omega
      have inbound : i < mask.size := by simpa [← ByteArray.size_data] using hi
      have access : mask[i]! = mask.data[i]'(by simpa only [ByteArray.size_data] using inbound) := by
        rw [getElem!_pos mask i inbound]
        rfl
      by_cases choice : mask.data[i]'(by simpa only [ByteArray.size_data] using inbound) = 1
      all_goals
        interval_cases i <;>
          simp [crop, tornBytes, fourBytes, selected, rawByte, ← ByteArray.size_data,
            ByteArray.get, choice, access]
      all_goals rfl
  · contradiction


theorem crop_torn_size (value : U16) (a b c d : Bool) (length : Nat) (bound : length ≤ 4) :
    (crop (tornBytes value a b c d) length).size = length := by
  simpa [crop, tornBytes, fourBytes, ← ByteArray.size_data] using bound

/-- Every prefix length uses an admissible seek/read/EOF script. Complete torn
records use the integrity proof; all shorter records use actual EOF rejection. -/
theorem recover_prefix (value : U16) (a b c d : Bool) (length : Nat)
    (bound : length ≤ 4) (rest : Term) (highWater : Nat) :
    let data := crop (tornBytes value a b c d) length
    let image : Image := ⟨data, highWater⟩
    let file : NativeFile := ⟨highWater + 1⟩
    recover_record file (restarted image (recoveryScript data rest)) =
      (.ok (.Ok none, file), fileEnv ({} : Environment) file (finished data rest) []) ∨
    recover_record file (restarted image (recoveryScript data rest)) =
      (.ok (.Ok (some value), file), fileEnv ({} : Environment) file (finished data rest) []) := by
  dsimp only
  by_cases short : length < 4
  · left
    rw [restart_as_fileEnv]
    exact recover_truncated _ ({} : Environment) [] _ rest 0 (by simp [Separate])
      (by rw [crop_torn_size _ _ _ _ _ _ bound]; exact short) (by simp [limit])
  · have full : length = 4 := by omega
    subst length
    simpa [crop, recoveryScript, scanning, eofPlan, finished, reading,
      tornBytes, fourBytes, readScript, ← ByteArray.size_data] using recover_torn_default value a b c d rest highWater

@[expose] def encoded (value : U16) : ByteArray :=
  fourBytes (low value) (high value) (low (~~~value)) (high (~~~value))

/-- Every stored byte is either zero or the corresponding original record byte. -/
@[expose] def Fresh (value : U16) (data : ByteArray) : Prop :=
  data.size ≤ 4 ∧ ∀ i, i < data.size → data[i]! = 0 ∨ data[i]! = (encoded value)[i]!

/-- Read the exact byte selected by an admitted persistence operation. -/
theorem persist_at (old visible mask result : ByteArray)
    (accepted : persist old visible mask = some result) (i : Nat) (inside : i < result.size) :
    result[i]! = if mask[i]! == 1 then visible[i]! else old[i]! := by
  unfold persist at accepted
  split at accepted
  · cases accepted
    have inbound : i < mask.size := by simpa [← ByteArray.size_data] using inside
    rw [getElem!_pos (⟨mask.data.mapIdx fun index choice =>
      if choice == 1 then visible[index]! else old[index]!⟩ : ByteArray) i inside,
      getElem!_pos mask i inbound]
    change (mask.data.mapIdx _)[i] = _
    simp only [_root_.Array.getElem_mapIdx]
    rfl
  · contradiction

/-- Fresh-slot integrity is closed under repeated background persistence, not
only a single mask applied to an initially empty durable image. -/
theorem persist_fresh (value : U16) (old visible mask result : ByteArray)
    (oldFresh : Fresh value old) (visibleFresh : Fresh value visible)
    (accepted : persist old visible mask = some result) : Fresh value result := by
  have size := persist_size old visible mask result accepted
  have bound := visibleFresh.1
  refine ⟨by omega, ?_⟩
  intro i inside
  rw [persist_at old visible mask result accepted i inside]
  split
  · exact visibleFresh.2 i (by omega)
  · by_cases oldBound : i < old.size
    · exact oldFresh.2 i oldBound
    · left
      rw [getElem!_neg old i (by omega)]
      rfl

/-- The byte invariant supplies all four zero/new choices for complete images
and the corresponding prefixes for every shorter image. -/
theorem classify_fresh (value : U16) (data : ByteArray) (fresh : Fresh value data) :
    data = crop (tornBytes value (data[0]! != 0) (data[1]! != 0)
      (data[2]! != 0) (data[3]! != 0)) data.size := by
  apply ByteArray.ext
  apply _root_.Array.ext
  · simpa [crop, tornBytes, fourBytes, ← ByteArray.size_data] using fresh.1
  · intro i hi hj
    have inbound : i < data.size := by simpa only [ByteArray.size_data] using hi
    have range : i < 4 := by have := fresh.1; omega
    have access : data[i]! = data.data[i]'hi := by
      rw [getElem!_pos data i inbound]
      rfl
    by_cases zero : data[i]! = 0
    · interval_cases i <;>
        simp [crop, tornBytes, fourBytes, selected, rawByte, ← ByteArray.size_data,
          ← access, zero]
    · have original := (fresh.2 i inbound).resolve_left zero
      interval_cases i <;>
        simp [crop, tornBytes, fourBytes, selected, rawByte, ← ByteArray.size_data, ← access, zero]
      all_goals exact original.trans (by rfl)

theorem fresh_empty (value : U16) : Fresh value ByteArray.empty := by
  simp [Fresh, ← ByteArray.size_data]

theorem fresh_encoded (value : U16) : Fresh value (encoded value) := by
  refine ⟨by simp [encoded, fourBytes, ← ByteArray.size_data], ?_⟩
  intro i inside
  exact Or.inr rfl

/-- A crash may add another persistence step after any number of earlier steps.
Both images are checked against the same original input record. -/
theorem crash_fresh (value : U16) (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State) (mask : ByteArray) (image : Image)
    (separate : Separate file frame) (valid : Valid state)
    (visibleFresh : Fresh value state.visible) (durableFresh : Fresh value state.durable)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    Fresh value image.bytes := by
  unfold crashImage at captured
  rw [lookup_at env file state frame separate valid] at captured
  change (persist state.durable state.visible mask).bind (fun durable =>
    some (⟨durable, (fileEnv env file state frame).refCounter⟩ : Image)) = some image at captured
  obtain ⟨durable, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  exact persist_fresh value state.durable state.visible mask durable durableFresh visibleFresh accepted

/-- The actual recovery handles every image satisfying the persistence invariant,
including all incomplete lengths and all repeated zero/new tearing histories. -/
theorem recover_fresh (value : U16) (image : Image) (rest : Term)
    (fresh : Fresh value image.bytes) :
    let file : NativeFile := ⟨image.highWater + 1⟩
    recover_record file (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok none, file), fileEnv ({} : Environment) file (finished image.bytes rest) []) ∨
    recover_record file (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (some value), file), fileEnv ({} : Environment) file (finished image.bytes rest) []) := by
  have shape := classify_fresh value image.bytes fresh
  have proof := recover_prefix value (image.bytes[0]! != 0) (image.bytes[1]! != 0)
    (image.bytes[2]! != 0) (image.bytes[3]! != 0) image.bytes.size fresh.1 rest image.highWater
  rw [← shape] at proof
  exact proof

/-- Crash capture, fresh runtime admission and actual Rust recovery compose.
The caller supplies no shape assumption or contract for the recovered image. -/
theorem crash_recovery (value : U16) (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State) (mask : ByteArray) (image : Image)
    (rest : Term) (separate : Separate file frame) (valid : Valid state)
    (visibleFresh : Fresh value state.visible) (durableFresh : Fresh value state.durable)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    restart image (recoveryScript image.bytes rest) = some
      (⟨image.highWater + 1⟩, restarted image (recoveryScript image.bytes rest)) ∧
    (recover_record ⟨image.highWater + 1⟩ (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok none, ⟨image.highWater + 1⟩), fileEnv ({} : Environment) ⟨image.highWater + 1⟩
        (finished image.bytes rest) []) ∨
    recover_record ⟨image.highWater + 1⟩ (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (some value), ⟨image.highWater + 1⟩), fileEnv ({} : Environment) ⟨image.highWater + 1⟩
        (finished image.bytes rest) [])) := by
  have fresh := crash_fresh value file env frame state mask image separate valid visibleFresh durableFresh captured
  constructor
  · apply restart_state image _
    have := fresh.1
    simp only [limit]
    omega
  · exact recover_fresh value image rest fresh


/-- Taking a prefix preserves the byte invariant for partial writes. -/
theorem fresh_crop (value : U16) (data : ByteArray) (length : Nat)
    (fresh : Fresh value data) : Fresh value (crop data length) := by
  have bound : (crop data length).size ≤ data.size := by
    simp [crop, ← ByteArray.size_data]
  refine ⟨by have := fresh.1; omega, ?_⟩
  intro i inside
  have inbound : i < data.size := by omega
  have same : (crop data length)[i]! = data[i]! := by
    rw [getElem!_pos _ i inside, getElem!_pos data i inbound]
    have insideArray : i < (data.data.extract 0 length).size := by
      simpa only [crop, ← ByteArray.size_data] using inside
    have inboundArray : i < data.data.size := by simpa only [ByteArray.size_data] using inbound
    change (data.data.extract 0 length)[i]'insideArray = data.data[i]'inboundArray
    rw [_root_.Array.getElem_extract]
    simp
  rw [same]
  exact fresh.2 i inbound

@[expose] def payload (value : U16) : Slice U8 :=
  .from (layout value).val (by simp [layout]; scalar_tac)

theorem payload_bytes (value : U16) : bytes (payload value) = encoded value := by
  simp [bytes, payload, layout, encoded, fourBytes, rawByte]

theorem overwrite_empty (data : ByteArray) (length : Nat) :
    overwrite ByteArray.empty 0 data length = crop data length := by
  by_cases zero : length = 0
  · subst length
    simp [overwrite, crop]
    rfl
  · apply ByteArray.ext
    simp [overwrite, crop, zero]
    apply _root_.Array.toList_inj.mp
    simp

/-- A successful caller, including a short write, commits exactly the supplied
encoded prefix. The returned Bool is derived from the actual Rust branch. -/
theorem write_record_success (file : NativeFile) (value : U16)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (amount : Nat) (mask durable syncMask : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : amount ≤ (payload value).val.length)
    (buffer : (payload value).val.length ≤ limit) (position : before.position + amount ≤ limit)
    (script : before.script = outcome "write" true amount mask (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes (payload value)) amount) mask = some durable) :
    write_record file value (fileEnv env file before frame) =
      (.ok (.Ok (decide (amount = 4)), file),
        fileEnv env file (committed before (payload value) amount rest) frame) := by
  have proof := write_record_ready file value env frame before
    (written before (payload value) amount durable (outcome "sync_all" true 0 syncMask rest))
    (committed before (payload value) amount rest) (count (payload value) amount bounded)
    separate valid
    (written_valid before (payload value) amount mask durable _ valid bounded position accepted)
    (by simp [blocked, script, outcome]) (by simp [blocked, written, outcome])
    (write_step before (payload value) amount mask durable _ bounded buffer position
      (by rw [script]; exact action_outcome _ _ _ _ _) accepted)
    (sync_step _ syncMask rest (action_outcome _ _ _ _ _))
  simpa [count] using proof

/-- Both the synchronized prefix and any earlier permitted persistence satisfy
the invariant. The image shape is derived from the original Rust input bytes. -/
theorem written_fresh (value : U16) (before : State) (amount : Nat)
    (mask durable : ByteArray) (rest : Term)
    (emptyVisible : before.visible = ByteArray.empty) (emptyDurable : before.durable = ByteArray.empty)
    (start : before.position = 0)
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes (payload value)) amount) mask = some durable) :
    Fresh value (written before (payload value) amount durable rest).visible ∧
    Fresh value (written before (payload value) amount durable rest).durable := by
  have visible : Fresh value (overwrite before.visible before.position (bytes (payload value)) amount) := by
    rw [emptyVisible, start, payload_bytes, overwrite_empty]
    exact fresh_crop value (encoded value) amount (fresh_encoded value)
  exact ⟨visible, persist_fresh value before.durable _ mask durable
    (emptyDurable ▸ fresh_empty value) visible accepted⟩


/-- A full original record returns its payload, rather than merely allowing it. -/
theorem recover_encoded (value : U16) (image : Image) (rest : Term)
    (intact : image.bytes = encoded value) :
    recover_record ⟨image.highWater + 1⟩ (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (some value), ⟨image.highWater + 1⟩), fileEnv ({} : Environment) ⟨image.highWater + 1⟩
        (finished image.bytes rest) []) := by
  have proof := recover_four (⟨image.highWater + 1⟩ : NativeFile) ({} : Environment) []
    (low value) (high value) (low (~~~value)) (high (~~~value)) rest 0
    (by simp [Separate]) (by simp [limit])
  rw [decode_layout] at proof
  rw [restart_as_fileEnv]
  simpa [intact, encoded, recoveryScript, scanning, eofPlan, reading, finished,
    fourBytes, readScript, NativeM.ok, ← ByteArray.size_data] using proof

/-- The actual writer's acknowledgement, every admitted post-sync crash and
actual recovery compose for all full and partial accepted write counts. -/
theorem write_record_crash (file : NativeFile) (value : U16)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (amount : Nat) (mask durable syncMask crashMask : ByteArray) (rest : Term) (image : Image)
    (separate : Separate file frame) (bounded : amount ≤ 4)
    (emptyVisible : before.visible = ByteArray.empty) (emptyDurable : before.durable = ByteArray.empty)
    (start : before.position = 0)
    (script : before.script = outcome "write" true amount mask (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes (payload value)) amount) mask = some durable)
    (captured : crashImage file crashMask
      (fileEnv env file (committed before (payload value) amount rest) frame) = some image) :
    write_record file value (fileEnv env file before frame) =
      (.ok (.Ok (decide (amount = 4)), file),
        fileEnv env file (committed before (payload value) amount rest) frame) ∧
    recover_record ⟨image.highWater + 1⟩ (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (if amount = 4 then some value else none), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ (finished image.bytes rest) []) := by
  have valid : Valid before := by
    simp [Valid, emptyVisible, emptyDurable, start, limit, ← ByteArray.size_data]
  have inputBound : amount ≤ (payload value).val.length := by
    simpa [payload, layout] using bounded
  have position : before.position + amount ≤ limit := by
    simp only [start, Nat.zero_add, limit]
    omega
  constructor
  · exact write_record_success file value env frame before amount mask durable syncMask rest
      separate valid inputBound (by simp [payload, layout, limit]) position script accepted
  · have afterValid : Valid (committed before (payload value) amount rest) := by
      simp [Valid, committed, emptyVisible, start, payload_bytes, overwrite_empty,
        crop, encoded, fourBytes, ← ByteArray.size_data, limit]
      omega
    have stable := (stable_image file env frame (committed before (payload value) amount rest)
      crashMask image separate afterValid rfl captured).1
    have shape : image.bytes = crop (encoded value) amount := by
      simpa [committed, emptyVisible, start, payload_bytes, overwrite_empty] using stable
    have size : image.bytes.size = amount := by
      rw [shape]
      simpa [crop, encoded, fourBytes, ← ByteArray.size_data] using bounded
    by_cases full : amount = 4
    · simp only [full, ite_true]
      apply recover_encoded value image rest
      simpa [full, crop, encoded, fourBytes] using shape
    · simp only [full, ite_false]
      rw [restart_as_fileEnv]
      apply recover_truncated _ ({} : Environment) [] image.bytes rest 0 (by simp [Separate])
      · omega
      · simp [limit]


/-- Before synchronization, an actual extracted write may leave any permitted
torn durable prefix. Capture and restart still cannot recover another payload. -/
theorem write_once_crash (file : NativeFile) (value : U16)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (amount : Nat) (mask durable crashMask : ByteArray) (writeRest recoveryRest : Term) (image : Image)
    (separate : Separate file frame) (bounded : amount ≤ 4)
    (emptyVisible : before.visible = ByteArray.empty) (emptyDurable : before.durable = ByteArray.empty)
    (start : before.position = 0)
    (script : before.script = outcome "write" true amount mask writeRest)
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes (payload value)) amount) mask = some durable)
    (captured : crashImage file crashMask
      (fileEnv env file (written before (payload value) amount durable writeRest) frame) = some image) :
    io_core.write_once file (payload value) (fileEnv env file before frame) =
      (.ok (.Ok (count (payload value) amount (by simpa [payload, layout] using bounded)), file),
        fileEnv env file (written before (payload value) amount durable writeRest) frame) ∧
    restart image (recoveryScript image.bytes recoveryRest) = some
      (⟨image.highWater + 1⟩, restarted image (recoveryScript image.bytes recoveryRest)) ∧
    (recover_record ⟨image.highWater + 1⟩ (restarted image (recoveryScript image.bytes recoveryRest)) =
      (.ok (.Ok none, ⟨image.highWater + 1⟩), fileEnv ({} : Environment) ⟨image.highWater + 1⟩
        (finished image.bytes recoveryRest) []) ∨
    recover_record ⟨image.highWater + 1⟩ (restarted image (recoveryScript image.bytes recoveryRest)) =
      (.ok (.Ok (some value), ⟨image.highWater + 1⟩), fileEnv ({} : Environment) ⟨image.highWater + 1⟩
        (finished image.bytes recoveryRest) [])) := by
  have valid : Valid before := by
    simp [Valid, emptyVisible, emptyDurable, start, limit, ← ByteArray.size_data]
  have inputBound : amount ≤ (payload value).val.length := by
    simpa [payload, layout] using bounded
  have position : before.position + amount ≤ limit := by
    simp only [start, Nat.zero_add, limit]
    omega
  have step := write_step before (payload value) amount mask durable writeRest inputBound
    (by simp [payload, layout, limit]) position (script ▸ action_outcome _ _ _ _ _) accepted
  have ready : pollWrite file (payload value) (fileEnv env file before frame) =
      some (.ok (.Ok (count (payload value) amount inputBound), file),
        fileEnv env file (written before (payload value) amount durable writeRest) frame) := by
    simp [pollWrite, lookup_at env file before frame separate valid, blocked, script, outcome,
      step, store_at env file before _ frame separate]
  constructor
  · simp only [io_core.write_once, monadLift_self, NativeFile.write]
    rw [Result.wait_ready_apply _ _ _ _ _ ready]
    simp
  · have fresh := written_fresh value before amount mask durable writeRest
      emptyVisible emptyDurable start accepted
    exact crash_recovery value file env frame _ crashMask image recoveryRest separate
      (written_valid before (payload value) amount mask durable writeRest valid inputBound position accepted)
      fresh.1 fresh.2 captured

end Record.CrashProperties
