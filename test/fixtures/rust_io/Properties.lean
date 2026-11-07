module
public import Disk.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Disk.Properties
open NativeFile

@[expose] def Valid (state : State) : Prop :=
  state.visible.size ≤ limit ∧ state.durable.size ≤ state.visible.size ∧ state.position ≤ limit

@[expose] def outcome (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if success then "ok" else "error"),
    .integer value, .bitstring mask 0]) rest

theorem action_outcome (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) :
    action operation (outcome operation success value mask rest) = some (success, value, mask, rest) := by
  cases success <;> simp [action, outcome]

theorem decode_encode (state : State) (valid : Valid state) :
    decode (encode state) = some state := by
  obtain ⟨visible, durable, position⟩ := valid
  have durableBound := Nat.le_trans durable visible
  simp [decode, encode, not_lt.mpr visible, not_lt.mpr durableBound, not_lt.mpr position]

@[expose] def fileEnv (env : Environment) (file : NativeFile) (state : State)
    (frame : List (Nat × String × Term)) : Environment :=
  { env with
    refCounter := Nat.max env.refCounter file.id
    nativeHeap := (file.id, typeName, encode state) :: frame }

@[expose] def Separate (file : NativeFile) (frame : List (Nat × String × Term)) : Prop :=
  ∀ cell ∈ frame, cell.1 ≠ file.id

theorem lookup_at (env : Environment) (file : NativeFile) (state : State)
    (frame : List (Nat × String × Term)) (separate : Separate file frame) (valid : Valid state) :
    lookup file (fileEnv env file state frame) = some state := by
  have filtered : frame.filter (fun cell => cell.1 == file.id) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro cell member
    simpa using separate cell member
  simp [lookup, fileEnv, List.filter, filtered, decode_encode state valid]

theorem store_at (env : Environment) (file : NativeFile) (before after : State)
    (frame : List (Nat × String × Term)) (separate : Separate file frame) :
    store file after (fileEnv env file before frame) = fileEnv env file after frame := by
  have unchanged : frame.map (fun cell =>
      if cell.1 = file.id then (file.id, typeName, encode after) else cell) = frame := by
    conv_rhs => rw [← List.map_id frame]
    apply List.map_congr_left
    intro cell member
    simp [separate cell member]
  simp [store, fileEnv, unchanged]

theorem bytes_size (data : Slice U8) : (bytes data).size = data.val.length := by
  simp [bytes, ← ByteArray.size_data]

theorem overwrite_size (old data : ByteArray) (position count : Nat) (bound : count ≤ data.size) :
    (overwrite old position data count).size =
      if count = 0 then old.size else max old.size (position + count) := by
  by_cases zero : count = 0
  · simp [overwrite, zero]
  · simp only [overwrite, zero, ↓reduceIte, ← ByteArray.size_data]
    simp only [List.size_toArray, List.length_append, List.length_take, List.length_replicate,
      List.length_drop, Array.length_toList]
    simp only [← ByteArray.size_data] at bound
    omega

theorem persist_size (old visible mask result : ByteArray) (accepted : persist old visible mask = some result) :
    result.size = mask.size ∧ mask.size ≤ max old.size visible.size := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    cases accepted
    constructor
    · simp [← ByteArray.size_data]
    · simpa only [← ByteArray.size_data] using conditions.2.1
  · contradiction

theorem cross_contract (file : NativeFile) (data : Slice U8) :
    write_then_sync file data = (do
      let (written, file) ← NativeFile.write file data
      match written with
      | .Err error => Result.ok (.Err error, file)
      | .Ok count => do
        let synced ← NativeFile.syncAll file
        match synced with
        | .Err error => Result.ok (.Err error, file)
        | .Ok () => Result.ok (.Ok count, file)) := by
  simp only [write_then_sync, io_core.write_once, io_core.synchronize, NativeM.ok, monadLift_self]
  apply congrArg (fun next => NativeFile.write file data >>= next)
  funext output
  rcases output with ⟨reply, file⟩
  cases reply with
  | Err error => rfl
  | Ok count =>
    apply congrArg (fun next => NativeFile.syncAll file >>= next)
    funext reply
    cases reply with
    | Err error => rfl
    | Ok value => cases value; rfl

@[expose] def count (data : Slice U8) (value : Nat) (bounded : value ≤ data.val.length) : Usize :=
  Usize.ofNatCore value (by have := data.property; scalar_tac)

@[expose] def written (before : State) (data : Slice U8) (value : Nat)
    (durable : ByteArray) (rest : Term) : State :=
  ⟨overwrite before.visible before.position (bytes data) value,
    durable, before.position + value, rest⟩

theorem written_valid (before : State) (data : Slice U8) (value : Nat)
    (mask durable : ByteArray) (rest : Term) (valid : Valid before)
    (bounded : value ≤ data.val.length) (position : before.position + value ≤ limit)
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes data) value) mask = some durable) :
    Valid (written before data value durable rest) := by
  have size := overwrite_size before.visible (bytes data) before.position value
    (by simpa only [bytes_size] using bounded)
  have persisted := persist_size _ _ _ _ accepted
  have oldBound : before.durable.size ≤ (overwrite before.visible before.position (bytes data) value).size := by
    rw [size]
    obtain ⟨_, old, _⟩ := valid
    split <;> omega
  rw [max_eq_right oldBound] at persisted
  unfold Valid written
  dsimp
  constructor
  · rw [size]
    split <;> simp_all [Valid] <;> omega
  · exact ⟨by omega, position⟩

theorem write_step (before : State) (data : Slice U8) (value : Nat)
    (mask durable : ByteArray) (rest : Term)
    (bounded : value ≤ data.val.length) (buffer : data.val.length ≤ limit)
    (position : before.position + value ≤ limit)
    (choice : action "write" before.script = some (true, value, mask, rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes data) value) mask = some durable) :
    writeStep before data = some (.Ok (count data value bounded),
      written before data value durable rest) := by
  simp [writeStep, choice, not_lt.mpr buffer, bounded, not_lt.mpr position,
    accepted, count, written]

theorem sync_step (before : State) (mask : ByteArray) (rest : Term)
    (choice : action "sync_all" before.script = some (true, 0, mask, rest)) :
    syncStep before = some (.Ok (), { before with durable := before.visible, script := rest }) := by
  simp [syncStep, choice]

/-- This composes the actual two-crate Rust implementation with ready write and
sync transitions. Neither an I/O error nor an invalid model choice can satisfy it. -/
theorem protocol_ready (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term))
    (before middle after : State) (amount : Usize)
    (separate : Separate file frame) (initial : Valid before) (intermediate : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (writeReady : writeStep before data = some (.Ok amount, middle))
    (syncReady : syncStep middle = some (.Ok (), after)) :
    write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Ok amount, file), fileEnv env file after frame) := by
  have first : pollWrite file data (fileEnv env file before frame) =
      some (.ok (.Ok amount, file), fileEnv env file middle frame) := by
    simp [pollWrite, lookup_at env file before frame separate initial, notBlocked,
      writeReady, store_at env file before middle frame separate]
  have second : pollSync file (fileEnv env file middle frame) =
      some (.ok (.Ok ()), fileEnv env file after frame) := by
    simp [pollSync, lookup_at env file middle frame separate intermediate, notBlockedMiddle,
      syncReady, store_at env file middle after frame separate]
  rw [cross_contract]
  unfold NativeFile.write
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ first]
  simp only [Result.ok_bind]
  unfold NativeFile.syncAll
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ second]
  simp [Result.ok_bind, Result.ok_apply]

/-- Every acknowledged prefix is synchronized by the actual Rust caller. The
returned count may be smaller than the input length. Unrelated heap cells survive. -/
theorem protocol_success (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (value : Nat) (mask durable syncMask : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : value ≤ data.val.length) (buffer : data.val.length ≤ limit)
    (position : before.position + value ≤ limit)
    (script : before.script = outcome "write" true value mask
      (outcome "sync_all" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes data) value) mask = some durable) :
    write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Ok (count data value bounded), file), fileEnv env file
        ⟨overwrite before.visible before.position (bytes data) value,
          overwrite before.visible before.position (bytes data) value,
          before.position + value, rest⟩ frame) := by
  apply protocol_ready file data env frame before
    (written before data value durable (outcome "sync_all" true 0 syncMask rest))
    _ (count data value bounded) separate valid
  · exact written_valid before data value mask durable _ valid bounded position accepted
  · simp [blocked, script, outcome]
  · simp [blocked, written, outcome]
  · apply write_step before data value mask durable _ bounded buffer position
    · rw [script, action_outcome]
    · exact accepted
  · apply sync_step
    exact action_outcome "sync_all" true 0 syncMask rest

/-- A write error returns unchanged visible bytes and offset, does not execute
sync, and preserves any background persistence permitted by the write outcome. -/
theorem protocol_write_error (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (error : Nat) (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (buffer : data.val.length ≤ limit)
    (script : before.script = outcome "write" false error mask rest)
    (accepted : persist before.durable before.visible mask = some durable) :
    write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Err ⟨error⟩, file), fileEnv env file
        { before with durable := durable, script := rest } frame) := by
  have ready : pollWrite file data (fileEnv env file before frame) =
      some (.ok (.Err ⟨error⟩, file), fileEnv env file
        { before with durable := durable, script := rest } frame) := by
    simp [pollWrite, lookup_at env file before frame separate valid,
      blocked, script, outcome, writeStep, action, not_lt.mpr (Int.natCast_nonneg error),
      not_lt.mpr buffer, accepted,
      store_at env file before _ frame separate]
  rw [cross_contract]
  unfold NativeFile.write
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ ready]
  simp [Result.ok_bind, Result.ok_apply]

/-- A sync error is propagated, retaining the visible prefix but making no full
persistence acknowledgement. The error outcome may itself persist a torn image. -/
theorem protocol_sync_error (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term))
    (before middle after : State) (amount : Usize) (error : NativeIoError)
    (separate : Separate file frame) (initial : Valid before) (intermediate : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (writeReady : writeStep before data = some (.Ok amount, middle))
    (syncReady : syncStep middle = some (.Err error, after)) :
    write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Err error, file), fileEnv env file after frame) := by
  have first : pollWrite file data (fileEnv env file before frame) =
      some (.ok (.Ok amount, file), fileEnv env file middle frame) := by
    simp [pollWrite, lookup_at env file before frame separate initial, notBlocked,
      writeReady, store_at env file before middle frame separate]
  have second : pollSync file (fileEnv env file middle frame) =
      some (.ok (.Err error), fileEnv env file after frame) := by
    simp [pollSync, lookup_at env file middle frame separate intermediate, notBlockedMiddle,
      syncReady, store_at env file middle after frame separate]
  rw [cross_contract]
  unfold NativeFile.write
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ first]
  simp only [Result.ok_bind]
  unfold NativeFile.syncAll
  rw [Result.wait_bind, Result.wait_ready_apply _ _ _ _ _ second]
  simp [Result.ok_bind, Result.ok_apply]

/-- Unlike synchronization, the low-level Rust write alone may leave durability
unchanged. This proves the distinction against the extracted crate function. -/
theorem write_alone (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term))
    (before after : State) (amount : Usize)
    (separate : Separate file frame) (valid : Valid before)
    (notBlocked : blocked before = false)
    (ready : writeStep before data = some (.Ok amount, after)) :
    io_core.write_once file data (fileEnv env file before frame) =
      (.ok (.Ok amount, file), fileEnv env file after frame) := by
  have poll : pollWrite file data (fileEnv env file before frame) =
      some (.ok (.Ok amount, file), fileEnv env file after frame) := by
    simp [pollWrite, lookup_at env file before frame separate valid, notBlocked,
      ready, store_at env file before after frame separate]
  unfold io_core.write_once NativeFile.write
  simp only [monadLift_self]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_apply]

end Disk.Properties
