module
public import Recovery.ReadProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Recovery.RecoveryProperties
open NativeFile Recovery.Properties Recovery.ReadProperties

/-- Once synchronized, every admitted subsequent persistence choice has the
same image. This quantifies every mask accepted by the declared tearing model. -/
theorem persist_same (bytes mask result : ByteArray)
    (accepted : persist bytes bytes mask = some result) : result = bytes := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    have size : mask.size = bytes.size := by omega
    cases accepted
    apply ByteArray.ext
    apply _root_.Array.ext
    · simp [size]
    · intro index validMask validBytes
      have bounded : index < bytes.size := by simpa only [ByteArray.size_data] using validBytes
      simp [getElem!_pos, bounded]
      rfl
  · contradiction

@[expose] def sought (before : State) (offset : Nat) (durable : ByteArray) (rest : Term) : State :=
  { before with position := offset, durable := durable, script := rest }

theorem seek_start (before : State) (offset : U64) (mask durable : ByteArray) (rest : Term)
    (bounded : offset.val ≤ limit)
    (choice : action "seek" before.script = some (true, 0, mask, rest))
    (accepted : persist before.durable before.visible mask = some durable) :
    seekStep before (.start offset) = some (.Ok offset, sought before offset.val durable rest) := by
  simp [seekStep, seekTarget, choice, accepted, not_lt.mpr bounded,
    not_lt.mpr (Int.natCast_nonneg offset.val), sought]
  scalar_tac

theorem seek_next (file : NativeFile) (offset : U64) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (reply : core.result.Result U64 NativeIoError)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (step : seekStep before (.start offset) = some (reply, after))
    (next : core.result.Result U64 NativeIoError × NativeFile → NativeM α) :
    (io_core.seek_to file offset >>= next) (fileEnv env file before frame) =
      next (reply, file) (fileEnv env file after frame) := by
  have ready : pollSeek file (.start offset) (fileEnv env file before frame) =
      some (.ok (reply, file), fileEnv env file after frame) := by
    simp [pollSeek, lookup_at env file before frame separate valid, notBlocked,
      step, store_at env file before after frame separate]
  simp only [io_core.seek_to, io_core.seek_from, Recovery.Extraction.FileModel.seek,
    monadLift_self, NativeFile.seek, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp [Result.ok_bind]

/-- The actual recovery caller first seeks to zero, even if its incoming offset
was already at EOF, then invokes the actual cross-crate parser. -/
theorem recover_success (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (low high : UInt8) (tail : List UInt8)
    (seekMask mask1 mask2 durable0 durable1 durable2 : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (contents : before.visible.data.toList = low :: high :: tail)
    (script : before.script = outcome "seek" true 0 seekMask
      (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest)))
    (accepted0 : persist before.durable before.visible seekMask = some durable0)
    (accepted1 : persist durable0 before.visible mask1 = some durable1)
    (accepted2 : persist durable1 before.visible mask2 = some durable2) :
    recover_word file (fileEnv env file before frame) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), file), fileEnv env file
        (readState (readState (sought before 0 durable0
          (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest)))
          1 durable1 (outcome "read" true 1 mask2 rest)) 1 durable2 rest) frame) := by
  let reset := sought before 0 durable0
    (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest))
  have resetValid : Valid reset := by
    have persisted := persist_size _ _ _ _ accepted0
    rw [max_eq_right valid.2.1] at persisted
    unfold Valid reset sought
    dsimp
    obtain ⟨visible, _, _⟩ := valid
    exact ⟨visible, by omega, by simp [limit]⟩
  have step : seekStep before (.start 0#u64) = some (.Ok 0#u64, reset) := by
    apply seek_start before 0#u64 seekMask durable0 _ (by simp [limit]) _ accepted0
    simpa only using script ▸ action_outcome "seek" true 0 seekMask
      (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest))
  simp only [recover_word, monadLift_self]
  rw [seek_next file 0#u64 env frame before reset (.Ok 0#u64) separate valid
    (by simp [blocked, script, outcome]) step]
  apply parser_success file env frame reset low high tail mask1 mask2 durable1 durable2 rest
    separate resetValid
  · simpa [reset, sought] using contents
  · rfl
  · exact accepted1
  · exact accepted2

/-- A synchronized file cannot lose acknowledged bytes under any admitted
post-sync persistence choice, regardless of unrelated heap contents. -/
theorem stable_image (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (state : State) (mask : ByteArray) (image : Image)
    (separate : Separate file frame) (valid : Valid state) (stable : state.durable = state.visible)
    (captured : crashImage file mask (fileEnv env file state frame) = some image) :
    image.bytes = state.visible ∧ image.highWater = (fileEnv env file state frame).refCounter := by
  unfold crashImage at captured
  rw [lookup_at env file state frame separate valid] at captured
  change (persist state.durable state.visible mask).bind (fun durable =>
    some (⟨durable, (fileEnv env file state frame).refCounter⟩ : Image)) = some image at captured
  obtain ⟨durable, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  exact ⟨persist_same state.visible mask durable (stable ▸ accepted), rfl⟩

@[expose] def restarted (image : Image) (script : Term) : Environment := {
  refCounter := image.highWater + 1
  nativeHeap := [(image.highWater + 1, typeName, encode ⟨image.bytes, image.bytes, 0, script⟩)] }

theorem restart_state (image : Image) (script : Term) (bounded : image.bytes.size ≤ limit) :
    restart image script = some (⟨image.highWater + 1⟩, restarted image script) := by
  simp [restart, not_lt.mpr bounded, restarted]

/-- The restart discards VM messages, dictionaries, registrations, other native
cells, process state and scheduler choices rather than reusing the old machine. -/
theorem restart_volatile (image : Image) (script : Term) :
    (restarted image script).currentProcess = ({} : ProcessState) ∧
    (restarted image script).processes = [] ∧
    (restarted image script).nativeResourceTypes = [] ∧
    (restarted image script).schedule = [] := by
  repeat constructor

/-- Ghost freshness prevents an old native file capability accessing the new
file even when a physical descriptor number might be reused by the OS. -/
theorem restart_rejects_stale (image : Image) (script : Term) (old : NativeFile)
    (allocated : old.id ≤ image.highWater) :
    lookup old (restarted image script) = none := by
  have different : image.highWater + 1 ≠ old.id := by omega
  simp [lookup, restarted, different]

theorem restart_as_fileEnv (image : Image) (script : Term) :
    restarted image script = fileEnv ({} : Environment) ⟨image.highWater + 1⟩
      ⟨image.bytes, image.bytes, 0, script⟩ [] := by
  simp [restarted, fileEnv]

/-- Recovery of an admitted fresh file is grounded in the actual seek/read
caller. Every accepted durability choice during recovery preserves the image. -/
theorem restart_recovery (image : Image) (low high : UInt8) (tail : List UInt8)
    (seekMask mask1 mask2 : ByteArray) (rest : Term)
    (bounded : image.bytes.size ≤ limit)
    (contents : image.bytes.data.toList = low :: high :: tail)
    (accepted0 : persist image.bytes image.bytes seekMask = some image.bytes)
    (accepted1 : persist image.bytes image.bytes mask1 = some image.bytes)
    (accepted2 : persist image.bytes image.bytes mask2 = some image.bytes) :
    recover_word ⟨image.highWater + 1⟩ (restarted image
      (outcome "seek" true 0 seekMask
        (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest)))) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          ⟨image.bytes, image.bytes, 2, rest⟩ []) := by
  rw [restart_as_fileEnv]
  have valid : Valid (⟨image.bytes, image.bytes, 0,
      outcome "seek" true 0 seekMask
        (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest))⟩ : State) := by
    exact ⟨bounded, Nat.le_refl _, by simp [limit]⟩
  simpa [sought, readState] using recover_success ⟨image.highWater + 1⟩ ({} : Environment) []
    ⟨image.bytes, image.bytes, 0, outcome "seek" true 0 seekMask
      (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest))⟩ low high tail
    seekMask mask1 mask2 image.bytes image.bytes image.bytes rest
    (by simp [Separate]) valid contents rfl accepted0 accepted1 accepted2

@[expose] def committed (before : State) (data : Slice U8) (value : Nat) (rest : Term) : State :=
  ⟨overwrite before.visible before.position (bytes data) value,
    overwrite before.visible before.position (bytes data) value, before.position + value, rest⟩

/-- Compose the actual write/sync caller with every admitted post-ack crash
image. No previously acknowledged byte can be rolled back by a tearing choice. -/
theorem acknowledged_image (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (value : Nat) (mask durable syncMask crashMask : ByteArray) (rest : Term) (image : Image)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : value ≤ data.val.length) (buffer : data.val.length ≤ limit)
    (position : before.position + value ≤ limit)
    (script : before.script = outcome "write" true value mask (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes data) value) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (committed before data value rest) frame) = some image) :
    write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Ok (count data value bounded), file), fileEnv env file (committed before data value rest) frame) ∧
    image.bytes = overwrite before.visible before.position (bytes data) value := by
  constructor
  · exact protocol_success file data env frame before value mask durable syncMask rest
      separate valid bounded buffer position script accepted
  · have afterWrite := written_valid before data value mask durable rest valid bounded position accepted
    have finalValid : Valid (committed before data value rest) := by
      obtain ⟨visible, _, position⟩ := afterWrite
      exact ⟨visible, Nat.le_refl _, position⟩
    exact (stable_image file env frame (committed before data value rest) crashMask image
      separate finalValid rfl captured).1

/-- Composition through acknowledged implementation state, the crash relation,
fresh-file admission and the actual recovery implementation. The result is the
acknowledged leading word, not a separately supplied first-party specification. -/
theorem acknowledged_recovery (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (value : Nat) (mask durable syncMask crashMask : ByteArray) (rest : Term) (image : Image)
    (low high : UInt8) (tail : List UInt8) (seekMask readMask1 readMask2 : ByteArray)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : value ≤ data.val.length) (buffer : data.val.length ≤ limit)
    (position : before.position + value ≤ limit)
    (script : before.script = outcome "write" true value mask (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes data) value) mask = some durable)
    (captured : crashImage file crashMask (fileEnv env file (committed before data value rest) frame) = some image)
    (leading : (overwrite before.visible before.position (bytes data) value).data.toList = low :: high :: tail)
    (accepted0 : persist image.bytes image.bytes seekMask = some image.bytes)
    (accepted1 : persist image.bytes image.bytes readMask1 = some image.bytes)
    (accepted2 : persist image.bytes image.bytes readMask2 = some image.bytes) :
    write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Ok (count data value bounded), file), fileEnv env file (committed before data value rest) frame) ∧
    recover_word ⟨image.highWater + 1⟩ (restarted image
      (outcome "seek" true 0 seekMask
        (outcome "read" true 1 readMask1 (outcome "read" true 1 readMask2 rest)))) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ ⟨image.bytes, image.bytes, 2, rest⟩ []) := by
  obtain ⟨ran, disk⟩ := acknowledged_image file data env frame before value mask durable syncMask
    crashMask rest image separate valid bounded buffer position script accepted captured
  refine ⟨ran, ?_⟩
  have imageBound : image.bytes.size ≤ limit := by
    have stateValid := written_valid before data value mask durable rest valid bounded position accepted
    rw [disk]
    exact stateValid.1
  apply restart_recovery image low high tail seekMask readMask1 readMask2 rest imageBound
  · simpa only [disk] using leading
  · exact accepted0
  · exact accepted1
  · exact accepted2

theorem seek_from_contract (file : NativeFile) (origin : core.io.seek.SeekFrom) :
    io_core.seek_from file origin = NativeFile.seek file (match origin with
      | .Start offset => .start offset | .End offset => .end_ offset | .Current offset => .current offset) := by
  rfl

theorem recover_seek_error (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State) (error : NativeIoError)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (step : seekStep before (.start 0#u64) = some (.Err error, after)) :
    recover_word file (fileEnv env file before frame) =
      (.ok (.Err error, file), fileEnv env file after frame) := by
  simp only [recover_word, monadLift_self]
  rw [seek_next file 0#u64 env frame before after (.Err error) separate valid notBlocked step]
  simp [NativeM.ok, Result.ok_apply]

/-- Recovery is read-only on stable contents: a later crash can change the ghost
freshness counter but cannot change this file image. The recovery computation
here is the actual extracted Rust caller, not a separate abstract recovery rule. -/
theorem recovery_image_idempotent (image image2 : Image) (low high : UInt8) (tail : List UInt8)
    (seekMask mask1 mask2 crashMask : ByteArray) (rest : Term)
    (bounded : image.bytes.size ≤ limit)
    (contents : image.bytes.data.toList = low :: high :: tail)
    (accepted0 : persist image.bytes image.bytes seekMask = some image.bytes)
    (accepted1 : persist image.bytes image.bytes mask1 = some image.bytes)
    (accepted2 : persist image.bytes image.bytes mask2 = some image.bytes)
    (captured : crashImage ⟨image.highWater + 1⟩ crashMask
      (fileEnv ({} : Environment) ⟨image.highWater + 1⟩ ⟨image.bytes, image.bytes, 2, rest⟩ []) = some image2) :
    recover_word ⟨image.highWater + 1⟩ (restarted image
      (outcome "seek" true 0 seekMask (outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest)))) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ ⟨image.bytes, image.bytes, 2, rest⟩ []) ∧
    image2.bytes = image.bytes := by
  refine ⟨restart_recovery image low high tail seekMask mask1 mask2 rest bounded contents accepted0 accepted1 accepted2, ?_⟩
  exact (stable_image ⟨image.highWater + 1⟩ ({} : Environment) []
    ⟨image.bytes, image.bytes, 2, rest⟩ crashMask image2 (by simp [Separate])
    ⟨bounded, Nat.le_refl _, by simp [limit]⟩ rfl captured).1

@[expose] def zeroMask (bytes : ByteArray) : ByteArray := ⟨_root_.Array.replicate bytes.size 0⟩

theorem persist_zero (bytes : ByteArray) : persist bytes bytes (zeroMask bytes) = some bytes := by
  have conditions : bytes.size ≤ (zeroMask bytes).size ∧
      (zeroMask bytes).size ≤ bytes.size ∧
      ((zeroMask bytes).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [zeroMask, ← ByteArray.size_data]
  let result : ByteArray := ⟨(zeroMask bytes).data.mapIdx fun index choice =>
    if choice == 1 then bytes[index]! else bytes[index]!⟩
  have accepted : persist bytes bytes (zeroMask bytes) = some result := by
    unfold persist
    simp only [Nat.min_self, Nat.max_self]
    rw [if_pos conditions]
  rw [persist_same bytes (zeroMask bytes) result accepted] at accepted
  exact accepted

/-- A concrete admissible script witnesses that recovery success is not vacuous:
no accepted-mask hypotheses or assumed implementation contracts are supplied. -/
theorem restart_recovery_default (image : Image) (low high : UInt8) (tail : List UInt8) (rest : Term)
    (bounded : image.bytes.size ≤ limit)
    (contents : image.bytes.data.toList = low :: high :: tail) :
    recover_word ⟨image.highWater + 1⟩ (restarted image
      (outcome "seek" true 0 (zeroMask image.bytes)
        (outcome "read" true 1 (zeroMask image.bytes)
          (outcome "read" true 1 (zeroMask image.bytes) rest)))) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ ⟨image.bytes, image.bytes, 2, rest⟩ []) := by
  exact restart_recovery image low high tail _ _ _ rest bounded contents
    (persist_zero image.bytes) (persist_zero image.bytes) (persist_zero image.bytes)

@[expose] def two (low high : UInt8) : Slice U8 := .from [byteValue low, byteValue high] (by scalar_tac)

theorem two_bytes (low high : UInt8) : (bytes (two low high)).data.toList = [low, high] := by
  simp [bytes, two, byteValue]

theorem overwritten_two (before : State) (low high : UInt8) (position : before.position = 0) :
    (overwrite before.visible before.position (bytes (two low high)) 2).data.toList =
      low :: high :: before.visible.data.toList.drop 2 := by
  simp [overwrite, position, two_bytes]

/-- A full two-byte acknowledgement recovers the bytes supplied to the actual
Rust implementation. The leading-image condition is derived from those inputs,
not supplied as an assumed postcondition. Recovery masks are concretely valid. -/
theorem word_acknowledged_recovery (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (low high : UInt8)
    (mask durable syncMask crashMask : ByteArray) (rest : Term) (image : Image)
    (separate : Separate file frame) (valid : Valid before) (position : before.position = 0)
    (script : before.script = outcome "write" true 2 mask (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes (two low high)) 2) mask = some durable)
    (captured : crashImage file crashMask
      (fileEnv env file (committed before (two low high) 2 rest) frame) = some image) :
    write_then_sync file (two low high) (fileEnv env file before frame) =
      (.ok (.Ok 2#usize, file), fileEnv env file (committed before (two low high) 2 rest) frame) ∧
    recover_word ⟨image.highWater + 1⟩ (restarted image
      (outcome "seek" true 0 (zeroMask image.bytes)
        (outcome "read" true 1 (zeroMask image.bytes)
          (outcome "read" true 1 (zeroMask image.bytes) rest)))) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩ ⟨image.bytes, image.bytes, 2, rest⟩ []) := by
  have small : 2 ≤ (two low high).val.length := by simp [two]
  have bounded : (two low high).val.length ≤ limit := by simp [two, limit]
  have fits : before.position + 2 ≤ limit := by simp [position, limit]
  have counted : count (two low high) 2 small = 2#usize := by
    apply UScalar.eq_of_val_eq
    simp [count]
  simpa only [counted] using acknowledged_recovery file (two low high) env frame before 2
    mask durable syncMask crashMask rest image low high (before.visible.data.toList.drop 2)
    (zeroMask image.bytes) (zeroMask image.bytes) (zeroMask image.bytes)
    separate valid small bounded fits script accepted captured (overwritten_two before low high position)
    (persist_zero image.bytes) (persist_zero image.bytes) (persist_zero image.bytes)

end Recovery.RecoveryProperties
