module
public import Close.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Close.Properties
open NativeFile

@[expose] def outcome (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if success then "ok" else "error"),
    .integer value, .bitstring mask 0]) rest

theorem action_outcome (operation : String) (success : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) :
    action operation (outcome operation success value mask rest) = some (success, value, mask, rest) := by
  cases success <;> simp [action, outcome]

@[expose] def live (file : NativeFile) (state : State) : Environment :=
  {refCounter := file.id, nativeHeap := [(file.id, typeName, encode state)]}

@[expose] def closed (file : NativeFile) (state : State) : Environment :=
  {refCounter := file.id, nativeHeap := [(file.id, closedTypeName, encode state)]}

@[expose] def Valid (state : State) : Prop :=
  state.visible.size ≤ limit ∧ state.durable.size ≤ limit ∧ state.position ≤ limit

theorem decode_valid (state : State) (valid : Valid state) :
    decode (encode state) = some state := by
  obtain ⟨visible, durable, position⟩ := valid
  simp [decode, encode, not_lt.mpr visible, not_lt.mpr durable, not_lt.mpr position]

theorem close_next (file : NativeFile) (before after : State) (valid : Valid before)
    (ready : blocked before = false) (step : closeStep before = some after)
    (next : Unit → NativeM α) :
    (consume_file file >>= next) (live file before) = next () (closed file after) := by
  have poll : pollClose file (live file before) = some (.ok (), closed file after) := by
    simp [pollClose, lookup, live, decode_valid before valid, ready, step, retire, closed]
  simp only [consume_file, monadLift_self, NativeDrop.drop, close, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

/-- The implementation consumes the file on either OS close outcome. No sync is
inferred, and every admitted bytewise persistence choice is retained. -/
theorem explicit_close (file : NativeFile) (before : State) (valid : Valid before)
    (success : Bool) (value : Nat) (mask durable : ByteArray) (rest : Term)
    (script : before.script = outcome "close" success value mask rest)
    (status : success = true → value = 0)
    (accepted : persist before.durable before.visible mask = some durable) :
    consume_file file (live file before) =
      (.ok (), closed file {before with durable := durable, script := rest}) := by
  have step : closeStep before = some {before with durable := durable, script := rest} := by
    cases success <;> simp_all [closeStep, action_outcome]
  have result := close_next file before _ valid
    (by simp [blocked, script, outcome]) step Result.ok
  simpa [Result.bind_ok, Result.ok_apply] using result

/-- Compiler-inserted scope-exit destruction has the same consuming effect as
explicit destruction of the actual extracted Rust function. -/
theorem implicit_close_contract (file : NativeFile) :
    implicit_close file = consume_file file := by
  rfl

/-- No file operation, including a second destruction, accepts the stale handle. -/
theorem closed_capability (file : NativeFile) (state : State) :
    lookup file (closed file state) = none ∧
    pollClose file (closed file state) = some (.error .exhausted, closed file state) ∧
    pollSync file (closed file state) = some (.error .exhausted, closed file state) := by
  simp [lookup, closed, typeName, closedTypeName, handleTypeName, writableHandleTypeName, pollClose, pollSync]

/-- Every admitted ordinary I/O operation rejects a retired capability. -/
theorem closed_io (file : NativeFile) (state : State) (data : Slice U8)
    (origin : SeekFrom) (length : U64) :
    pollWrite file data (closed file state) = some (.error .exhausted, closed file state) ∧
    pollRead file data (closed file state) = some (.error .exhausted, closed file state) ∧
    pollSeek file origin (closed file state) = some (.error .exhausted, closed file state) ∧
    pollSetLen file length (closed file state) = some (.error .exhausted, closed file state) := by
  simp [pollWrite, pollRead, pollSeek, pollSetLen, (closed_capability file state).1]

theorem missing_close_choice (file : NativeFile) (state : State) (valid : Valid state)
    (missing : state.script = .nil) :
    pollClose file (live file state) = some (.error .exhausted, live file state) := by
  simp [pollClose, lookup, live, decode_valid state valid, blocked, missing, closeStep, action]

/-- Closing retains disk state for subsequent power-loss reasoning. The old id
here is a ghost observer; it grants no further file operations. -/
theorem closed_crash (file : NativeFile) (state : State) (valid : Valid state)
    (mask durable : ByteArray) (accepted : persist state.durable state.visible mask = some durable) :
    crashImage file mask (closed file state) = some ⟨durable, file.id⟩ := by
  unfold crashImage
  rw [(closed_capability file state).1]
  simp [lookupClosed, closed, decode_valid state valid, accepted]

/-- The actual cross-crate Rust caller preserves the sync result and always
consumes the file after either successful or failed synchronization. -/
theorem synchronize_close (file : NativeFile) (before middle after : State)
    (reply : core.result.Result Unit NativeIoError)
    (initial : Valid before) (intermediate : Valid middle)
    (ready : blocked before = false) (closeReady : blocked middle = false)
    (sync : syncStep before = some (reply, middle)) (finish : closeStep middle = some after) :
    synchronize_then_close file (live file before) = (.ok reply, closed file after) := by
  have poll : pollSync file (live file before) = some (.ok reply, live file middle) := by
    simp [pollSync, lookup, live, decode_valid before initial, ready, sync, store]
  simp only [synchronize_then_close, io_core.synchronize, monadLift_self, syncAll,
    Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp only [Result.ok_bind]
  change (consume_file file >>= fun _ => NativeM.ok reply) (live file middle) = _
  rw [close_next file middle after intermediate closeReady finish]
  simp [NativeM.ok]

/-- Closing an unsynchronized file can retain only its old durable byte, even
when close succeeds. A durability acknowledgment at close would be unsound. -/
theorem close_is_not_sync :
    consume_file ⟨1⟩ (live ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0,
      outcome "close" true 0 ⟨#[0]⟩ .nil⟩) =
    (.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩) := by
  exact explicit_close ⟨1⟩ _ (by unfold Valid; decide) true 0 ⟨#[0]⟩ ⟨#[1]⟩ .nil
    rfl (fun _ => rfl) (by decide)

/-- The host close failure is ignored by Rust drop, while ownership is still
consumed and no durability is invented. -/
theorem failed_close_consumes :
    consume_file ⟨1⟩ (live ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0,
      outcome "close" false 5 ⟨#[0]⟩ .nil⟩) =
    (.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩) := by
  exact explicit_close ⟨1⟩ _ (by unfold Valid; decide) false 5 ⟨#[0]⟩ ⟨#[1]⟩ .nil
    rfl (by simp) (by decide)

theorem blocked_close (file : NativeFile) (state : State) (valid : Valid state)
    (pending : state.script = .cons (.atom "blocked") .nil) :
    pollClose file (live file state) = none := by
  simp [pollClose, lookup, live, decode_valid state valid, blocked, pending]

/-- Explicit reopen is a host admission, with a fresh capability. The closed
handle cannot address the newly admitted file even if its bytes are identical. -/
theorem reopen_closed (file : NativeFile) (state : State) (valid : Valid state)
    (mask durable : ByteArray) (accepted : persist state.durable state.visible mask = some durable)
    (bounded : durable.size ≤ limit) (script : Term) :
    (crashImage file mask (closed file state)).bind (fun image => restart image script) =
      some (⟨file.id + 1⟩, {
        refCounter := file.id + 1
        nativeHeap := [(file.id + 1, typeName, encode ⟨durable, durable, 0, script⟩)] }) := by
  rw [closed_crash file state valid mask durable accepted]
  simp [restart, not_lt.mpr bounded]

/-- Compose the actual Rust destruction, stale-capability rejection, crash image
and fresh host reopening. Reopening is explicit admission, not a proved OS call. -/
theorem close_lifecycle (file : NativeFile) (before : State) (valid : Valid before)
    (success : Bool) (value : Nat) (mask durable : ByteArray) (rest : Term)
    (script : before.script = outcome "close" success value mask rest)
    (status : success = true → value = 0)
    (accepted : persist before.durable before.visible mask = some durable)
    (durableBound : durable.size ≤ limit)
    (crashMask recovered : ByteArray)
    (crashChoice : persist durable before.visible crashMask = some recovered)
    (recoveredBound : recovered.size ≤ limit) (reopenScript : Term) :
    consume_file file (live file before) =
      (.ok (), closed file {before with durable := durable, script := rest}) ∧
    lookup file (closed file {before with durable := durable, script := rest}) = none ∧
    (crashImage file crashMask (closed file {before with durable := durable, script := rest})).bind
      (fun image => restart image reopenScript) =
      some (⟨file.id + 1⟩, {
        refCounter := file.id + 1
        nativeHeap := [(file.id + 1, typeName, encode ⟨recovered, recovered, 0, reopenScript⟩)] }) := by
  refine ⟨explicit_close file before valid success value mask durable rest script status accepted,
    (closed_capability file _).1, ?_⟩
  exact reopen_closed file {before with durable := durable, script := rest}
    ⟨valid.1, durableBound, valid.2.2⟩ crashMask recovered
    crashChoice recoveredBound reopenScript

end Close.Properties
