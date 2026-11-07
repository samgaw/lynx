module
public import Read.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Read.ReadProperties
open NativeFile Read.Properties

@[expose] def one (byte : U8) : Slice U8 := .from [byte] (by scalar_tac)
@[expose] def word (low high : U8) : U16 :=
  core.num.U16.from_le_bytes (Array.make 2#usize [low, high])

/-- The actual low-level crate retains the file identity and the mutable buffer. -/
theorem read_next (file : NativeFile) (buffer : Slice U8) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (reply : core.result.Result Usize NativeIoError) (updated : Slice U8)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (step : readStep before buffer = some (reply, after, updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (io_core.read_once file buffer >>= next) (fileEnv env file before frame) =
      next (reply, file, updated) (fileEnv env file after frame) := by
  have ready : pollRead file buffer (fileEnv env file before frame) =
      some (.ok (reply, file, updated), fileEnv env file after frame) := by
    simp [pollRead, lookup_at env file before frame separate valid, notBlocked,
      step, store_at env file before after frame separate]
  simp only [io_core.read_once, monadLift_self, NativeFile.read, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp [Result.ok_bind]

/-- Unfold the real parser, including both mutable array reconstructions,
checked element projections and little-endian decoding. -/
theorem parser_ready (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before middle after : State) (low high : U8)
    (separate : Separate file frame) (valid : Valid before) (validMiddle : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one low))
    (second : readStep middle (one 0#u8) = some (.Ok 1#usize, after, one high)) :
    read_word file (fileEnv env file before frame) =
      (.ok (.Ok (some (word low high)), file), fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before middle _ (one low)
    separate valid notBlocked first]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame middle after _ (one high)
    separate validMiddle notBlockedMiddle second]
  simp [NativeM.ok, NativeM.lift, Array.from_slice, Array.to_slice_mut,
    one, Array.make_val, Array.index_usize, NativeM.monadLift_eq, NativeM.fromRust,
    word, Result.ok_bind, Result.ok_apply]

@[expose] def readState (before : State) (value : Nat) (durable : ByteArray) (rest : Term) : State :=
  { before with position := before.position + value, durable := durable, script := rest }

@[expose] def byteValue (byte : UInt8) : U8 :=
  U8.ofNatCore byte.toNat (by have := byte.toNat_lt; scalar_tac)

theorem read_one_step (before : State) (byte : UInt8) (tail : List UInt8)
    (mask durable : ByteArray) (rest : Term)
    (contents : before.visible.data.toList.drop before.position = byte :: tail)
    (choice : action "read" before.script = some (true, 1, mask, rest))
    (accepted : persist before.durable before.visible mask = some durable) :
    readStep before (one 0#u8) =
      some (.Ok 1#usize, readState before 1 durable rest, one (byteValue byte)) := by
  have length := congrArg List.length contents
  simp only [List.length_drop, Array.length_toList, List.length_cons] at length
  have available : 1 ≤ before.visible.size - before.position := by
    rw [← ByteArray.size_data]
    omega
  simp [readStep, one, choice, accepted, limit, available, readBuffer,
    contents, readState, byteValue]
  scalar_tac

theorem read_valid (before : State) (value : Nat) (mask durable : ByteArray) (rest : Term)
    (valid : Valid before) (bounded : value ≤ before.visible.size - before.position)
    (accepted : persist before.durable before.visible mask = some durable) :
    Valid (readState before value durable rest) := by
  have size := persist_size _ _ _ _ accepted
  rw [max_eq_right valid.2.1] at size
  obtain ⟨visible, old, position⟩ := valid
  unfold Valid readState
  dsimp
  constructor
  · exact visible
  · constructor <;> omega

/-- For any two leading file bytes and any accepted background persistence,
the actual parser returns exactly their little-endian word and advances twice. -/
theorem parser_success (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (low high : UInt8) (tail : List UInt8)
    (mask1 mask2 durable1 durable2 : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (contents : before.visible.data.toList.drop before.position = low :: high :: tail)
    (script : before.script = outcome "read" true 1 mask1 (outcome "read" true 1 mask2 rest))
    (accepted1 : persist before.durable before.visible mask1 = some durable1)
    (accepted2 : persist durable1 before.visible mask2 = some durable2) :
    read_word file (fileEnv env file before frame) =
      (.ok (.Ok (some (word (byteValue low) (byteValue high))), file), fileEnv env file
        (readState (readState before 1 durable1 (outcome "read" true 1 mask2 rest)) 1 durable2 rest) frame) := by
  let middle := readState before 1 durable1 (outcome "read" true 1 mask2 rest)
  apply parser_ready file env frame before middle _ (byteValue low) (byteValue high) separate valid
  · apply read_valid before 1 mask1 durable1 _ valid _ accepted1
    have length := congrArg List.length contents
    simp only [List.length_drop, Array.length_toList, List.length_cons] at length
    rw [← ByteArray.size_data]
    omega
  · simp [blocked, script, outcome]
  · simp [blocked, middle, readState, outcome]
  · apply read_one_step before low (high :: tail) mask1 durable1 _ contents _ accepted1
    rw [script, action_outcome]
  · apply read_one_step middle high tail mask2 durable2 rest _ _ accepted2
    · change before.visible.data.toList.drop (before.position + 1) = high :: tail
      rw [← List.drop_drop, contents]
      rfl
    · exact action_outcome "read" true 1 mask2 rest

theorem eof_step (before : State) (mask durable : ByteArray) (rest : Term)
    (eof : before.visible.size ≤ before.position)
    (choice : action "read" before.script = some (true, 0, mask, rest))
    (accepted : persist before.durable before.visible mask = some durable) :
    readStep before (one 0#u8) =
      some (.Ok 0#usize, readState before 0 durable rest, one 0#u8) := by
  simp [readStep, one, choice, accepted, limit, not_lt.mpr eof, readBuffer, readState]
  scalar_tac

theorem error_step (before : State) (error : Nat) (mask durable : ByteArray) (rest : Term)
    (choice : action "read" before.script = some (false, error, mask, rest))
    (accepted : persist before.durable before.visible mask = some durable) :
    readStep before (one 0#u8) =
      some (.Err ⟨error⟩, readState before 0 durable rest, one 0#u8) := by
  simp [readStep, one, choice, accepted, limit, readState]

/-- An empty file does not produce a word from the initialized zero buffer. -/
theorem parser_first_eof (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (first : readStep before (one 0#u8) = some (.Ok 0#usize, after, one 0#u8)) :
    read_word file (fileEnv env file before frame) =
      (.ok (.Ok none, file), fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before after _ _ separate valid notBlocked first]
  simp [NativeM.ok, Result.ok_apply]

/-- A one-byte suffix is incomplete, even when its initialized high byte is zero. -/
theorem parser_second_eof (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before middle after : State) (low : U8)
    (separate : Separate file frame) (valid : Valid before) (validMiddle : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one low))
    (second : readStep middle (one 0#u8) = some (.Ok 0#usize, after, one 0#u8)) :
    read_word file (fileEnv env file before frame) =
      (.ok (.Ok none, file), fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before middle _ _ separate valid notBlocked first]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame middle after _ _ separate validMiddle notBlockedMiddle second]
  simp [NativeM.ok, Result.ok_apply]

theorem parser_first_error (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State) (error : NativeIoError)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (first : readStep before (one 0#u8) = some (.Err error, after, one 0#u8)) :
    read_word file (fileEnv env file before frame) =
      (.ok (.Err error, file), fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before after _ _ separate valid notBlocked first]
  simp [NativeM.ok, Result.ok_apply]

theorem parser_second_error (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before middle after : State) (low : U8) (error : NativeIoError)
    (separate : Separate file frame) (valid : Valid before) (validMiddle : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one low))
    (second : readStep middle (one 0#u8) = some (.Err error, after, one 0#u8)) :
    read_word file (fileEnv env file before frame) =
      (.ok (.Err error, file), fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame before middle _ _ separate valid notBlocked first]
  change (io_core.read_once file (one 0#u8) >>= _) _ = _
  rw [read_next file (one 0#u8) env frame middle after _ _ separate validMiddle notBlockedMiddle second]
  simp [NativeM.ok, Result.ok_apply]

end Read.ReadProperties
