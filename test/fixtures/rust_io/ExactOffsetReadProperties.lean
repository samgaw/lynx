module
public import ExactOffsetRead.Extraction.Funs
public import Lynx.Concurrent
public section

open Aeneas Aeneas.Std Lynx Lynx.NativeFile io_protocol
namespace ExactOffsetRead.Properties

abbrev Reply := core.result.Result Unit NativeIoError × Slice U8
abbrev Cursor := (Slice U8 → Slice U8) × Slice U8 × U64

@[expose] def iteration (file : NativeFile) (cursor : Cursor) : NativeM (ControlFlow Cursor Reply) :=
  std.os.unix.fs.FileExt.read_exact_at.default_loop.body
    std.fs.File.Insts.StdOsUnixFsFileExt file cursor.1 cursor.2.1 cursor.2.2

@[expose] def joinSlice (updated : Slice U8) (amount : Usize) (suffix : Slice U8) : Slice U8 :=
  .from (updated.val.setSlice! amount.val suffix.val) (by simp)

private theorem suffix_borrow (updated : Slice U8) (amount : Usize)
    (fits : amount.val ≤ updated.val.length)
    (indices : core.slice.index.SliceIndex (core.ops.range.RangeFrom Usize) (Slice U8) (Slice U8))
    (same : indices.index_mut = core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut) :
    core.slice.index.Slice.index_mut indices updated (⟨amount⟩ : core.ops.range.RangeFrom Usize) =
        RustM.ok (updated.drop amount, joinSlice updated amount) := by
  simp [core.slice.index.Slice.index_mut, same,
    core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut, Slice.length, fits]
  rfl

@[expose] def eofError : NativeIoError := .staticMessage "UnexpectedEof"
  (NativeFile.bytes (toStr "failed to fill whole buffer"))

theorem eof_constant : core.io.error.Error.READ_EXACT_EOF = Result.ok eofError := by
  simp [core.io.error.Error.READ_EXACT_EOF, ExactOffsetRead.Extraction.IoErrorModel.fromStaticMessage,
    ExactOffsetRead.Extraction.IoErrorModel.encodeKind, core.hint.must_use, NativeM.ok, eofError]

private theorem buffer_length (state : NativeFile.State) (buffer : Slice U8) (count : Nat)
    (bounded : count ≤ buffer.val.length)
    (available : count ≤ state.visible.size - state.position) :
    (readBuffer state buffer count bounded available).val.length = buffer.val.length := by
  have length : (state.visible.data.toList.drop state.position |>.take count).length = count := by
    simp only [List.length_take, List.length_drop, Array.length_toList]
    simp only [← ByteArray.size_data] at available
    omega
  simp only [readBuffer, Slice.from_val, List.length_append, List.length_map, length, List.length_drop]
  omega

private theorem step_bounds (state next : NativeFile.State) (input updated : Slice U8)
    (count : Usize) (read : readStep state input true = some (.Ok count, next, updated)) :
    count.val ≤ updated.val.length ∧ count.val ≤ limit ∧
      updated.val.length = input.val.length := by
  simp only [readStep] at read
  repeat' first | split at read | simp_all [Option.bind_eq_bind, Option.bind]
  obtain ⟨rfl, rfl, rfl⟩ := read
  simp only [buffer_length, Usize.ofNatCore_val_eq]
  exact ⟨by omega, by omega, trivial⟩

private theorem poll_bounds (file returned : NativeFile) (input updated : Slice U8)
    (offset : U64) (before after : Environment) (amount : Usize)
    (read : pollRead file input before (some offset) = some (.ok (.Ok amount, returned, updated), after)) :
    amount.val ≤ updated.val.length ∧ offset.val ≤ limit ∧ amount.val ≤ limit ∧
      updated.val.length = input.val.length := by
  simp only [pollRead, Option.any, Option.elim, Option.isSome] at read
  split at read
  · simp at read
  split at read
  · simp at read
  split at read
  · simp at read
  · rename_i state _ _ offsetBound
    split at read
    · simp at read
    · rename_i result next suffix step
      simp only [Option.some.injEq, Prod.mk.injEq, Except.ok.injEq] at read
      obtain ⟨⟨rfl, _, rfl⟩, _⟩ := read
      have bounds := step_bounds _ _ _ _ _ step
      simp only [decide_eq_true_eq] at offsetBound
      exact ⟨bounds.1, by omega, bounds.2⟩

private theorem checked_advance (offset next : U64) (amount : Usize)
    (advanced : next.val = offset.val + amount.val) :
    offset + UScalar.cast .U64 amount = RustM.ok next := by
  have cast : (UScalar.cast .U64 amount).val = amount.val := by
    apply UScalar.cast_val_mod_pow_of_inBounds_eq
    have bound : next.val < 2 ^ 64 := by scalar_tac
    change amount.val < 2 ^ 64
    omega
  have spec := U64.add_bv_spec
      (x := offset) (y := UScalar.cast .U64 amount) (by
        rw [cast, ← advanced]
        scalar_tac)
  cases result : offset + UScalar.cast .U64 amount with
  | ret total =>
      rw [result, WP.spec_ok] at spec
      have same : total = next := by
        apply UScalar.eq_of_val_eq
        simpa only [cast, advanced] using spec.1
      rw [same]
  | vis eff next => simp [result] at spec
  | div => simp [result] at spec

private theorem kind_no_panic (error : NativeIoError) :
    NativeM.NoPanic (ExactOffsetRead.Extraction.IoErrorModel.kind error) := by
  simp only [ExactOffsetRead.Extraction.IoErrorModel.kind, NativeIoError.kind, Result.nativeGet_bind]
  apply NativeM.NoPanic.nativeGet
  intro env
  generalize h : NativeIoError.getKind error env = reply
  cases reply with
  | error exception =>
    have equal : exception = .exhausted := by
      cases error <;> simp only [NativeIoError.getKind] at h
      all_goals repeat' first | split at h | simp_all
    subst exception
    exact .exhausted
  | ok label =>
    simp only [Result.ofExcept_ok, Result.ok_bind, ExactOffsetRead.Extraction.IoErrorModel.decodeKind]
    split <;> first | exact NativeM.NoPanic.ok _ | exact NativeM.NoPanic.exhausted

private theorem poll_error (file : NativeFile) (buffer : Slice U8) (offset : U64)
    (before after : Environment) (exception : Exception)
    (read : pollRead file buffer before (some offset) = some (.error exception, after)) :
    exception = .exhausted := by
  simp only [pollRead] at read
  repeat' first | split at read | simp_all

private theorem step_no_panic (file : NativeFile) (back : Slice U8 → Slice U8)
    (input : Slice U8) (offset : U64) :
    NativeM.NoPanic (iteration file (back, input, offset)) := by
  simp only [iteration, std.os.unix.fs.FileExt.read_exact_at.default_loop.body,
    core.slice.Slice.is_empty, NativeM.monadLift_eq, NativeM.fromRust_ok,
    Result.ok_bind, monadLift_self]
  split
  · simp_all only [NativeM.ok]
    exact .ok _
  · change NativeM.NoPanic (readAt file input offset >>= _)
    simp only [readAt, Result.wait_bind]
    apply NativeM.NoPanic.wait
    intro env reply after read
    cases reply with
    | error exception =>
      have equal := poll_error file input offset env after exception read
      subst exception
      exact .exhausted
    | ok response =>
      obtain ⟨reply, returned, updated⟩ := response
      cases reply with
      | Ok amount =>
        simp only [Result.ok_bind]
        split
        · split
          · exact .ok _
          · simp only [eof_constant, NativeM.ok, Result.ok_bind]
            exact .ok _
        · have ⟨fits, offsetBound, amountBound, _⟩ := poll_bounds file returned input updated offset env after amount read
          let next := U64.ofNatCore (offset.val + amount.val) (by
            simp only [limit] at offsetBound amountBound
            scalar_tac)
          have advanced : next.val = offset.val + amount.val := by simp [next]
          rw [suffix_borrow updated amount fits]
          · simp only [checked_advance offset next amount advanced, NativeM.fromRust_ok,
              Result.ok_bind, NativeM.lift, NativeM.ok]
            exact .ok _
          · rfl
      | Err error =>
        simp only [Result.ok_bind, ExactOffsetRead.Extraction.IoErrorModel.isInterrupted,
          bind_assoc]
        apply NativeM.NoPanic.bind (kind_no_panic error)
        intro kind
        cases kind <;> simp only [NativeM.ok, Result.ok_bind, ↓reduceIte]
        all_goals first
          | exact .ok _
          | exact (NativeM.NoPanic.io_error_dispose error).bind _ (fun _ => .ok _)

private theorem loop_no_panic (file : NativeFile) (fuel : Nat) (cursor : Cursor) :
    NativeM.NoPanic (NativeM.loopFuel (iteration file) fuel cursor) := by
  induction fuel generalizing cursor with
  | zero => exact .exhausted
  | succ fuel ih =>
    rw [NativeM.loopFuel]
    apply NativeM.NoPanic.bind (step_no_panic file cursor.1 cursor.2.1 cursor.2.2)
    intro result
    cases result with
    | cont next => exact ih next
    | done reply => exact .ok reply

theorem fill_no_panic (file : NativeFile) (input : Slice U8) (offset : U64) :
    NativeM.NoPanic (io_protocol.io_core.positional.read_exact_at file input offset) := by
  change NativeM.NoPanic (NativeM.loopFuel (iteration file) 262145 (id, input, offset))
  exact loop_no_panic _ _ _

private theorem empty_step (file : NativeFile) (back : Slice U8 → Slice U8)
    (input : Slice U8) (offset : U64) (empty : input.val = []) :
    iteration file (back, input, offset) = .ok (.done (.Ok (), back input)) := by
  simp [iteration, std.os.unix.fs.FileExt.read_exact_at.default_loop.body,
    core.slice.Slice.is_empty, empty, monadLift_self, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind, NativeM.ok]

private theorem accepted_step (file returned : NativeFile) (back : Slice U8 → Slice U8)
    (input updated : Slice U8) (offset next : U64) (amount : Usize) (before after : Environment)
    (nonempty : input.val ≠ []) (positive : 0 < amount.val)
    (advanced : next.val = offset.val + amount.val)
    (read : pollRead file input before (some offset) = some (.ok (.Ok amount, returned, updated), after)) :
    Result.ReadyPrefix (iteration file (back, input, offset)) before
      (.ok (.cont (back ∘ joinSlice updated amount, updated.drop amount, next))) after := by
  have fits := (poll_bounds file returned input updated offset before after amount read).1
  have nonzero : input.length ≠ 0 := by simpa [Slice.length] using nonempty
  simp only [iteration, std.os.unix.fs.FileExt.read_exact_at.default_loop.body, monadLift_self,
    core.slice.Slice.is_empty, nonzero, decide_false, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind, Bool.false_eq_true, ↓reduceIte]
  change Result.ReadyPrefix (readAt file input offset >>= _) _ _ _
  simp only [readAt, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ read
  cases count : amount.val with
  | zero => omega
  | succ n =>
    simp only [Result.ok_bind, count]
    rw [suffix_borrow updated amount fits]
    · simp only [checked_advance offset next amount advanced, NativeM.fromRust_ok,
        Result.ok_bind, NativeM.lift, NativeM.ok]
      exact .refl _ _
    · rfl

/-- A finite plan of positive positional reads. The remaining buffer and
offset advance together, and each completed prefix is retained. -/
inductive Chunks (file : NativeFile) :
    Nat → Slice U8 → U64 → Environment → Slice U8 → Environment → Prop where
  | empty (input : Slice U8) (offset : U64) (env : Environment) (done : input.val = []) :
      Chunks file 0 input offset env input env
  | next {count : Nat} {input updated suffix : Slice U8} {offset nextOffset : U64}
      {returned : NativeFile} {amount : Usize} {before middle after : Environment}
      (nonempty : input.val ≠ []) (positive : 0 < amount.val)
      (advanced : nextOffset.val = offset.val + amount.val)
      (read : pollRead file input before (some offset) = some (.ok (.Ok amount, returned, updated), middle))
      (rest : Chunks file count (updated.drop amount) nextOffset middle suffix after) :
      Chunks file (count + 1) input offset before (joinSlice updated amount suffix) after

private theorem loop_follows {file : NativeFile} {count : Nat} {input output : Slice U8}
    {offset : U64} {before after : Environment}
    (plan : Chunks file count input offset before output after)
    (back : Slice U8 → Slice U8) (fuel : Nat) (finite : count < fuel) :
    Result.ReadyPrefix (NativeM.loopFuel (iteration file) fuel (back, input, offset))
      before (.ok (.Ok (), back output)) after := by
  induction plan generalizing back fuel with
  | empty input offset env done =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [NativeM.loopFuel, empty_step _ _ _ _ done, Result.ok_bind, NativeM.ok]
      exact .refl _ _
  | @next count input updated suffix offset nextOffset returned amount before middle after
      nonempty positive advanced read rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold NativeM.loopFuel
      have one := accepted_step file returned back input updated offset nextOffset amount
        before middle nonempty positive advanced read
      have advancedLoop := one.bind (fun result => match result with
        | .cont cursor => NativeM.loopFuel (iteration file) fuel cursor
        | .done reply => NativeM.ok reply)
      simp only [Result.ok_bind] at advancedLoop
      convert advancedLoop.trans (ih (back ∘ joinSlice updated amount) fuel (by omega)) using 1 <;> try rfl
      congr 1
      funext result
      cases result <;> rfl

/-- The actual standard default fills the initialized slice along every finite
admitted positive-read plan within the native loop budget. -/
theorem reads_all (file : NativeFile) (input : Slice U8) (offset : U64)
    {count : Nat} {before after : Environment} {output : Slice U8}
    (plan : Chunks file count input offset before output after) (finite : count < 262145) :
    Result.ReadyPrefix (io_protocol.io_core.positional.read_exact_at file input offset)
      before (.ok (.Ok (), output)) after := by
  change Result.ReadyPrefix (NativeM.loopFuel (iteration file) 262145 (id, input, offset))
    before (.ok (.Ok (), output)) after
  exact loop_follows plan _ _ finite

@[expose] def initial : Aeneas.Std.Array U8 2#usize := Aeneas.Std.Array.repeat 2#usize 0#u8

private def decode (result : Reply) : NativeM (core.result.Result U16 NativeIoError) :=
  match result with
  | (.Ok (), updated) => NativeM.ok (.Ok (core.num.U16.from_le_bytes (initial.from_slice updated)))
  | (.Err error, _) => NativeM.ok (.Err error)

private theorem caller_order (file : NativeFile) (offset : U64) :
    io_protocol.positional.observe_word file offset =
      (io_protocol.io_core.positional.read_exact_at file initial.to_slice offset >>= decode) := by
  simp only [io_protocol.positional.observe_word, monadLift_self,
    NativeM.lift, Result.ok_bind, Aeneas.Std.Array.to_slice_mut, initial]
  apply congrArg (fun next => io_protocol.io_core.positional.read_exact_at file _ offset >>= next)
  funext result
  obtain ⟨reply, updated⟩ := result
  cases reply with
  | Ok value => cases value; rfl
  | Err error =>
    simp [decode, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind, NativeM.ok]

theorem word_no_panic (file : NativeFile) (offset : U64) :
    NativeM.NoPanic (io_protocol.positional.observe_word file offset) := by
  rw [caller_order]
  apply NativeM.NoPanic.bind (fill_no_panic file initial.to_slice offset)
  intro result
  obtain ⟨reply, updated⟩ := result
  cases reply with
  | Ok value => cases value; exact .ok _
  | Err _ => exact .ok _

private theorem Chunks.length_eq {file : NativeFile} {count : Nat} {input output : Slice U8}
    {offset : U64} {before after : Environment}
    (plan : Chunks file count input offset before output after) :
    output.val.length = input.val.length := by
  cases plan with
  | empty => rfl
  | next _ _ _ read _ =>
    have bounds := poll_bounds _ _ _ _ _ _ _ _ read
    simpa only [joinSlice, Slice.from_val, List.length_setSlice!] using bounds.2.2.2

theorem decodes_complete (file : NativeFile) (offset : U64)
    {count : Nat} {before after : Environment} {output : Slice U8}
    (plan : Chunks file count initial.to_slice offset before output after) (finite : count < 262145) :
    Result.ReadyPrefix (io_protocol.positional.observe_word file offset)
      before (.ok (.Ok (core.num.U16.from_le_bytes
        (.from output.val (by simpa [initial, Aeneas.Std.Array.to_slice] using plan.length_eq))))) after := by
  rw [caller_order]
  refine ((reads_all file initial.to_slice offset plan finite).bind decode).trans ?_
  have size : output.val.length = (2#usize : Usize).val := by
    simpa [initial, Aeneas.Std.Array.to_slice] using plan.length_eq
  have same : initial.from_slice output = .from output.val size := by
    simp [Aeneas.Std.Array.from_slice, size]
  simp only [decode, Result.ok_bind, same, NativeM.ok]
  exact .refl _ _

@[expose] def action (status : Bool) (value : Nat) (length : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom "read_at", .atom (if status then "ok" else "error"),
    .integer value, .bitstring (ByteArray.mk (Array.replicate length 0)) 0]) rest

@[expose] def world (bytes : ByteArray) (script : Term)
    (classification : Option String := none) : Environment :=
  { nativeRefCounter := 8
    nativeHeap := [(1, typeName, encode ⟨bytes, bytes, 5, script⟩)] ++
      match classification with
      | none => []
      | some kind => [(7, NativeIoError.typeName, .atom "live"),
          (8, NativeIoError.kindTypeName, NativeIoError.kindEntry (.os 7) kind)] }

@[expose] def record (observe : NativeFile → U64 → NativeM (core.result.Result U16 NativeIoError))
    (offset : U64) : Result Term := do
  match ← observe ⟨1⟩ offset with
  | .Ok word => Result.ok (.integer word.val)
  | .Err (.staticMessage kind _) => Result.ok (.atom kind)
  | .Err (.os code) => Result.ok (.tuple #[.atom "os", .integer code])
  | .Err (.simple kind) => Result.ok (.tuple #[.atom "simple", .atom kind])

@[expose] def stateAfter (reply : Term) (bytes : ByteArray) (remaining : Term) (hasError : Bool)
    (cfg : Concurrent.Config Term) : Bool :=
  let env := match cfg with
    | .start env .. => env
    | .running state .. => state.nativeView []
  match cfg.outcome, NativeFile.lookup ⟨1⟩ env with
  | .ok value, some file =>
    value.identical reply && file.visible.data == bytes.data && file.durable.data == bytes.data &&
      file.position == 5 && file.script.identical remaining &&
      env.nativeHeap.any (fun cell => cell.1 == 7 && cell.2.1 == NativeIoError.typeName) == hasError
  | _, _ => false

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem short_reads_decode (elapsed : PID → Nat → Nat) :
    let bytes := ByteArray.mk #[99, 7, 8, 55]
    let short := action true 1 4
    Concurrent.checkPost (stateAfter (.integer 2055) bytes .nil false) 32
      (.start (world bytes (short (short .nil))) (record io_protocol.positional.observe_word 1#u64) elapsed) = true := by
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem interrupted_read_retries (elapsed : PID → Nat → Nat) :
    let bytes := ByteArray.mk #[99, 7, 8, 55]
    let short := action true 1 4
    Concurrent.checkPost (stateAfter (.integer 2055) bytes .nil false) 32
      (.start (world bytes (short (action false 7 4 (short .nil))) (some "Interrupted"))
        (record io_protocol.positional.observe_word 1#u64) elapsed) = true := by
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem short_eof_is_truncated (elapsed : PID → Nat → Nat) :
    let bytes := ByteArray.mk #[99, 7]
    let sentinel := action true 0 2 .nil
    Concurrent.checkPost (stateAfter (.atom "UnexpectedEof") bytes sentinel false) 32
      (.start (world bytes (action true 1 2 (action true 0 2 sentinel))) (record io_protocol.positional.observe_word 1#u64) elapsed) = true := by
  cbv

@[expose] def reportBuffer (fill : NativeM Reply) : Result Term := do
  let (reply, updated) ← fill
  match reply with
  | .Err (.staticMessage kind _) => Result.ok (.tuple #[.atom kind, .bitstring (bytes updated) 0])
  | _ => Result.ok (.atom "unexpected")

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem eof_retains_initialized_suffix (elapsed : PID → Nat → Nat) :
    let visible := ByteArray.mk #[99, 7]
    let result := Term.tuple #[.atom "UnexpectedEof", .bitstring ⟨#[7, 0]⟩ 0]
    Concurrent.checkPost (stateAfter result visible .nil false) 32
      (.start (world visible (action true 1 2 (action true 0 2 .nil)))
        (reportBuffer (io_protocol.io_core.positional.read_exact_at ⟨1⟩ initial.to_slice 1#u64))
        elapsed) = true := by
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem failed_read_leaves_tail (elapsed : PID → Nat → Nat) :
    let bytes := ByteArray.mk #[99, 7, 8, 55]
    let sentinel := action true 1 4 .nil
    Concurrent.checkPost (stateAfter (.tuple #[.atom "os", .integer 7]) bytes sentinel true) 32
      (.start (world bytes (action true 1 4 (action false 7 4 sentinel)) (some "InputOutputError"))
        (record io_protocol.positional.observe_word 1#u64) elapsed) = true := by
  cbv

end ExactOffsetRead.Properties
