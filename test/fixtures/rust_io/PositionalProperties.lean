module
public import Positional.Base
public section
open Aeneas Aeneas.Std Lynx
open Lynx.NativeFile Positional.Properties
namespace Positional.Proofs

/-- The extracted patch propagates either error and acknowledges only the count
returned by the original positional write. -/
theorem patch_order (file : NativeFile) (offset : U64) (data : Slice U8) :
    io_protocol.positional.patch file offset data = (do
      let written ← writeAt file data offset
      match written with
      | .Err error => Result.ok (.Err error)
      | .Ok amount =>
        let synced ← syncData file
        match synced with
        | .Ok () => Result.ok (.Ok amount)
        | .Err error => Result.ok (.Err error)) := by
  simp only [io_protocol.positional.patch, io_protocol.io_core.positional.write_at, monadLift_self]
  apply congrArg (fun next => writeAt file data offset >>= next)
  funext written
  cases written with
  | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
  | Ok amount =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch, NativeM.monadLift_eq,
      NativeM.fromRust_ok, Result.ok_bind]
    apply congrArg (fun next => syncData file >>= next)
    funext synced
    cases synced with
    | Err error => simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame, NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
    | Ok accepted => cases accepted; rfl

theorem observe_contract (file : NativeFile) (offset : U64) (buffer : Slice U8) :
    io_protocol.positional.observe file offset buffer = readAt file buffer offset := by
  simp [io_protocol.positional.observe, io_protocol.io_core.positional.read_at, monadLift_self]

private theorem patch_from_steps (file : NativeFile) (data : Slice U8) (offset : U64)
    (env : Environment) (frame : List (Nat × String × Term))
    (before middle after : State) (amount : Usize) (reply : core.result.Result Unit NativeIoError)
    (separate : Separate file frame) (initial : Valid before)
    (bounded : offset.val ≤ limit) (ready : blocked before = false)
    (writeReady : writeStep {before with position := offset.val} data true =
      some (.Ok amount, middle))
    (validMiddle : Valid {middle with position := before.position})
    (readyMiddle : blocked middle = false)
    (syncReady : syncStep {middle with position := before.position} true = some (reply, after)) :
    io_protocol.positional.patch file offset data (fileEnv env file before frame) =
      (.ok (match reply with | .Ok () => .Ok amount | .Err error => .Err error),
        fileEnv env file after frame) := by
  have first : pollWrite file data (fileEnv env file before frame) (some offset) =
      some (.ok (.Ok amount, file), fileEnv env file {middle with position := before.position} frame) := by
    simp [-getHandle, pollWrite, lookup_at env file before frame separate initial,
      ready, not_lt.mpr bounded, writeReady, no_shared_handle_at env file before frame separate,
      store_at env file before {middle with position := before.position} frame separate]
  have second : pollSync file (fileEnv env file {middle with position := before.position} frame) true =
      some (.ok reply, fileEnv env file after frame) := by
    have sameBlocked : blocked {middle with position := before.position} = false := readyMiddle
    simp [pollSync, lookup_at env file _ frame separate validMiddle, sameBlocked,
      syncReady, store_at env file _ after frame separate]
  rw [patch_order]
  unfold writeAt
  dsimp only
  rw [Result.wait_bind, Result.wait_ready_run _ _ _ _ _ first]
  simp only [Result.ok_bind]
  unfold syncData
  rw [Result.wait_bind, Result.wait_ready_run _ _ _ _ _ second]
  cases reply with
  | Ok result => cases result; simp [Result.ok_bind, Result.ok_apply]
  | Err error => simp [Result.ok_bind, Result.ok_apply]

/-- In this independent descriptor world, successful positional writes and
subsequent sync preserve unrelated cells and the descriptor's original cursor. -/
theorem patch_ready (file : NativeFile) (data : Slice U8) (offset : U64)
    (env : Environment) (frame : List (Nat × String × Term))
    (before middle after : State) (amount : Usize)
    (separate : Separate file frame) (initial : Valid before)
    (bounded : offset.val ≤ limit) (ready : blocked before = false)
    (writeReady : writeStep {before with position := offset.val} data true =
      some (.Ok amount, middle))
    (validMiddle : Valid {middle with position := before.position})
    (readyMiddle : blocked middle = false)
    (syncReady : syncStep {middle with position := before.position} true = some (.Ok (), after)) :
    io_protocol.positional.patch file offset data (fileEnv env file before frame) =
      (.ok (.Ok amount), fileEnv env file after frame) := by
  exact patch_from_steps file data offset env frame before middle after amount (.Ok ())
    separate initial bounded ready writeReady validMiddle readyMiddle syncReady

/-- All bytes in an acknowledged image survive any admitted crash mask.
A short write changes only its accepted prefix at the requested offset. -/
theorem patch_persists_prefix (file : NativeFile) (data : Slice U8) (offset : U64)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (amount : Nat) (mask durable syncMask : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (countBound : amount ≤ data.val.length) (bufferBound : data.val.length ≤ limit)
    (positionBound : offset.val + amount ≤ limit)
    (script : before.script = outcome "write_at" true amount mask
      (outcome "sync_data" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible offset.val (bytes data) amount) mask = some durable) :
    let updated := overwrite before.visible offset.val (bytes data) amount
    let after := fileEnv env file ⟨updated, updated, before.position, rest⟩ frame
    io_protocol.positional.patch file offset data (fileEnv env file before frame) =
      (.ok (.Ok (count data amount countBound)), after) ∧
    ∀ crashMask image, crashImage file crashMask after = some image → image.bytes = updated := by
  intro updated after
  let middle : State :=
    ⟨updated, durable, offset.val + amount, outcome "sync_data" true 0 syncMask rest⟩
  have offsetBound : offset.val ≤ limit := by omega
  have shifted : Valid {before with position := offset.val} := ⟨valid.1, valid.2.1, offsetBound⟩
  have writtenValid : Valid middle :=
    written_valid {before with position := offset.val} data amount mask durable _ shifted
      countBound positionBound accepted
  have finalValid : Valid (⟨updated, updated, before.position, rest⟩ : State) :=
    ⟨writtenValid.1, Nat.le_refl _, valid.2.2⟩
  constructor
  · apply patch_ready file data offset env frame before middle _ _ separate valid offsetBound
    · simp [blocked, script, outcome]
    · simp [writeStep, script, action_outcome, countBound, not_lt.mpr bufferBound,
        not_lt.mpr positionBound, accepted, middle, updated, count]
    · exact ⟨writtenValid.1, writtenValid.2.1, valid.2.2⟩
    · simp [blocked, middle, outcome]
    · simp [syncStep, middle, action_outcome]
  · intro crashMask image captured
    unfold crashImage at captured
    dsimp only [after] at captured
    rw [lookup_at env file _ frame separate finalValid] at captured
    change (persist updated updated crashMask).bind (fun saved =>
      some (⟨saved, after.nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨saved, choice, result⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj result
    exact persist_same _ _ _ choice

/-- A successful positional write followed by a failed synchronization reports
that error, preserves the accepted write's visible bytes and cursor, and keeps
exactly the persistence admitted by the failing host operation. -/
theorem patch_sync_error (file : NativeFile) (data : Slice U8) (offset : U64)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (amount error : Nat) (writeMask written syncMask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (countBound : amount ≤ data.val.length) (bufferBound : data.val.length ≤ limit)
    (positionBound : offset.val + amount ≤ limit)
    (script : before.script = outcome "write_at" true amount writeMask
      (outcome "sync_data" false error syncMask rest))
    (writtenBytes : persist before.durable
      (overwrite before.visible offset.val (bytes data) amount) writeMask = some written)
    (syncedBytes : persist written
      (overwrite before.visible offset.val (bytes data) amount) syncMask = some durable) :
    let visible := overwrite before.visible offset.val (bytes data) amount
    let after := fileEnv env file ⟨visible, durable, before.position, rest⟩ frame
    io_protocol.positional.patch file offset data (fileEnv env file before frame) =
      (.ok (.Err (.os error)), after) ∧
    ∀ crashMask image, crashImage file crashMask after = some image →
      persist durable visible crashMask = some image.bytes := by
  intro visible after
  let middle : State :=
    ⟨visible, written, offset.val + amount, outcome "sync_data" false error syncMask rest⟩
  have offsetBound : offset.val ≤ limit := by omega
  have shifted : Valid {before with position := offset.val} := ⟨valid.1, valid.2.1, offsetBound⟩
  have writtenValid : Valid middle :=
    written_valid {before with position := offset.val} data amount writeMask written _ shifted
      countBound positionBound writtenBytes
  have admitted : persist written visible syncMask = some durable := syncedBytes
  have fits : written.size ≤ visible.size := writtenValid.2.1
  have durableBound : durable.size ≤ visible.size := by
    obtain ⟨equalSize, maskFits⟩ := persist_size written visible syncMask durable admitted
    rw [equalSize]
    simpa only [max_eq_right fits] using maskFits
  have finalValid : Valid (⟨visible, durable, before.position, rest⟩ : State) :=
    ⟨writtenValid.1, durableBound, valid.2.2⟩
  constructor
  · apply patch_from_steps file data offset env frame before middle _ (count data amount countBound) (.Err (.os error))
      separate valid offsetBound
    · simp [blocked, script, outcome]
    · simp [writeStep, script, action_outcome, countBound, not_lt.mpr bufferBound,
        not_lt.mpr positionBound, writtenBytes, middle, visible, count]
    · exact ⟨writtenValid.1, writtenValid.2.1, valid.2.2⟩
    · simp [blocked, middle, outcome]
    · simp [syncStep, middle, action_outcome, admitted]
  · intro crashMask image captured
    unfold crashImage at captured
    dsimp only [after] at captured
    rw [lookup_at env file _ frame separate finalValid] at captured
    change (persist durable visible crashMask).bind (fun saved =>
      some (⟨saved, after.nativeRefCounter⟩ : Image)) = some image at captured
    obtain ⟨saved, choice, result⟩ := Option.bind_eq_some_iff.mp captured
    cases Option.some.inj result
    exact choice

/-- An actual positional read retains the original cursor and exposes only the
selected mutation of the buffer and the admitted background persistence step. -/
theorem observe_ready (file : NativeFile) (offset : U64) (buffer : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term))
    (before after : State) (reply : core.result.Result Usize NativeIoError)
    (output : Slice U8) (separate : Separate file frame) (valid : Valid before)
    (bounded : offset.val ≤ limit) (ready : blocked before = false)
    (step : readStep {before with position := offset.val} buffer true = some (reply, after, output)) :
    io_protocol.positional.observe file offset buffer (fileEnv env file before frame) =
      (.ok (reply, output), fileEnv env file {after with position := before.position} frame) := by
  have poll : pollRead file buffer (fileEnv env file before frame) (some offset) =
      some (.ok (reply, file, output), fileEnv env file {after with position := before.position} frame) := by
    simp [pollRead, lookup_at env file before frame separate valid, ready, not_lt.mpr bounded,
      step, store_at env file before {after with position := before.position} frame separate]
  rw [observe_contract]
  unfold readAt
  dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp [Result.ok_apply]

theorem observe_prefix (file : NativeFile) (offset : U64) (buffer : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (amount : Nat) (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : offset.val ≤ limit) (bufferBound : buffer.val.length ≤ limit)
    (positive : 0 < amount) (fits : amount ≤ buffer.val.length)
    (available : amount ≤ before.visible.size - offset.val)
    (script : before.script = outcome "read_at" true amount mask rest)
    (persisted : persist before.durable before.visible mask = some durable) :
    io_protocol.positional.observe file offset buffer (fileEnv env file before frame) =
      (.ok (.Ok (count buffer amount fits),
        readBuffer {before with position := offset.val} buffer amount fits available),
        fileEnv env file {before with durable := durable, script := rest} frame) := by
  apply observe_ready file offset buffer env frame before
    {before with position := offset.val + amount, durable := durable, script := rest}
    _ _ separate valid bounded
  · simp [blocked, script, outcome]
  · simp [readStep, script, action_outcome, not_lt.mpr bufferBound, persisted,
      fits, available, Nat.ne_of_gt positive, count]

theorem observe_eof (file : NativeFile) (offset : U64) (buffer : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : offset.val ≤ limit) (bufferBound : buffer.val.length ≤ limit)
    (endOfFile : before.visible.size ≤ offset.val)
    (script : before.script = outcome "read_at" true 0 mask rest)
    (persisted : persist before.durable before.visible mask = some durable) :
    io_protocol.positional.observe file offset buffer (fileEnv env file before frame) =
      (.ok (.Ok 0#usize, buffer),
        fileEnv env file {before with durable := durable, script := rest} frame) := by
  have untouched (state : State) : readBuffer state buffer 0 (by simp) (by simp) =
      buffer := by
    apply Slice.ext
    simp [readBuffer]
  apply observe_ready file offset buffer env frame before
    {before with position := offset.val, durable := durable, script := rest}
    _ _ separate valid bounded
  · simp [blocked, script, outcome]
  · simp [readStep, script, action_outcome, not_lt.mpr bufferBound, persisted,
      not_lt.mpr endOfFile, untouched, Usize.ofNatCore]

theorem observe_error (file : NativeFile) (offset : U64) (buffer : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (error : Nat) (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : offset.val ≤ limit) (bufferBound : buffer.val.length ≤ limit)
    (script : before.script = outcome "read_at" false error mask rest)
    (persisted : persist before.durable before.visible mask = some durable) :
    io_protocol.positional.observe file offset buffer (fileEnv env file before frame) =
      (.ok (.Err (.os error), buffer),
        fileEnv env file {before with durable := durable, script := rest} frame) := by
  apply observe_ready file offset buffer env frame before
    {before with position := offset.val, durable := durable, script := rest}
    _ _ separate valid bounded
  · simp [blocked, script, outcome]
  · simp [readStep, script, action_outcome, not_lt.mpr bufferBound, persisted]

/-- A failed positional write consumes only its failure outcome. Its prior bytes
and cursor are unchanged and the following sync is never executed. -/
theorem patch_write_error (file : NativeFile) (offset : U64) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (error : Nat) (mask durable : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : offset.val ≤ limit) (bufferBound : data.val.length ≤ limit)
    (script : before.script = outcome "write_at" false error mask rest)
    (persisted : persist before.durable before.visible mask = some durable) :
    io_protocol.positional.patch file offset data (fileEnv env file before frame) =
      (.ok (.Err (.os error)), fileEnv env file {before with durable := durable, script := rest} frame) := by
  have ready : pollWrite file data (fileEnv env file before frame) (some offset) =
      some (.ok (.Err (.os error), file),
        fileEnv env file {before with durable := durable, script := rest} frame) := by
    have unblocked : blocked before = false := by simp [blocked, script, outcome]
    simp [pollWrite, lookup_at env file before frame separate valid, unblocked,
      not_lt.mpr bounded, writeStep, script, action_outcome, not_lt.mpr bufferBound,
      persisted, store_at env file before _ frame separate]
  rw [patch_order]
  unfold writeAt
  dsimp only
  rw [Result.wait_bind, Result.wait_ready_run _ _ _ _ _ ready]
  simp [Result.ok_bind, Result.ok_apply]

theorem observe_outside (file : NativeFile) (offset : U64) (buffer : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (separate : Separate file frame) (valid : Valid before)
    (large : limit < offset.val) (ready : blocked before = false) :
    io_protocol.positional.observe file offset buffer (fileEnv env file before frame) =
      (.error .exhausted, fileEnv env file before frame) := by
  have poll : pollRead file buffer (fileEnv env file before frame) (some offset) =
      some (.error .exhausted, fileEnv env file before frame) := by
    simp [pollRead, lookup_at env file before frame separate valid, ready, large]
  rw [observe_contract]
  unfold readAt
  dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp [Result.error_apply]

end Positional.Proofs
