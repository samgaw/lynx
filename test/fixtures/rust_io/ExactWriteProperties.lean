module
public import ExactWrite.Extraction.Funs
public import Lynx.Concurrent
public section

open Aeneas Aeneas.Std Lynx Lynx.NativeFile io_protocol
namespace ExactWrite.Properties

abbrev Reply := core.result.Result Unit NativeIoError
abbrev Cursor := Slice U8 × U64

@[expose] def iteration (file : NativeFile) (input : Cursor) :
    NativeM (ControlFlow Cursor Reply) :=
  std.os.unix.fs.FileExt.write_all_at.default_loop.body
    std.fs.File.Insts.StdOsUnixFsFileExt file input.1 input.2

theorem empty_step (file : NativeFile) (input : Slice U8) (offset : U64)
    (empty : input.val = []) :
    iteration file (input, offset) = .ok (.done (.Ok ())) := by
  simp [iteration, std.os.unix.fs.FileExt.write_all_at.default_loop.body,
    core.slice.Slice.is_empty, empty, monadLift_self, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind, NativeM.ok]

private theorem index_suffix (input : Slice U8) (amount : Usize)
    (fits : amount.val ≤ input.val.length) :
      core.slice.index.Slice.index (ExactWrite.Extraction.SliceModel.rangeFrom U8)
        input (⟨amount⟩ : core.ops.range.RangeFrom Usize) = RustM.ok (input.drop amount) := by
  simpa [core.slice.index.Slice.index,
      ExactWrite.Extraction.SliceModel.rangeFrom, Slice.length] using
      ExactWrite.Extraction.SliceModel.indexFrom_valid ⟨amount⟩ input (by simpa [Slice.length] using fits)

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

theorem accepted_step (file : NativeFile) (input : Slice U8) (offset next : U64)
    (amount : Usize) (before after : Environment)
    (positive : 0 < amount.val) (fits : amount.val ≤ input.val.length)
    (advanced : next.val = offset.val + amount.val)
    (ready : pollWrite file input before (some offset) = some (.ok (.Ok amount, file), after)) :
    Result.ReadyPrefix (iteration file (input, offset)) before
      (.ok (.cont (input.drop amount, next))) after := by
  have nonempty : input.val ≠ [] := by intro empty; simp [empty] at fits; omega
  have suffix := index_suffix input amount fits
  have sum := checked_advance offset next amount advanced
  have nonzero : input.length ≠ 0 := by simpa [Slice.length] using nonempty
  simp only [iteration, std.os.unix.fs.FileExt.write_all_at.default_loop.body, monadLift_self,
    core.slice.Slice.is_empty, nonzero, decide_false, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind, Bool.false_eq_true, ↓reduceIte]
  change Result.ReadyPrefix (writeAt file input offset >>= _) _ _ _
  simp only [writeAt, Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ ready
  cases h : amount.val with
  | zero => omega
  | succ n =>
    simp only [h, suffix, sum,
      NativeM.fromRust_ok, Result.ok_bind, NativeM.lift, NativeM.ok]
    exact Result.ReadyPrefix.refl _ _

/-- A finite plan of successful positional calls. Each positive response
advances the offset and supplies only the unwritten suffix to the next call. -/
inductive Chunks (file : NativeFile) : Nat → Cursor → Environment → Environment → Prop where
  | empty (input : Slice U8) (offset : U64) (env : Environment) (done : input.val = []) :
      Chunks file 0 (input, offset) env env
  | next {count : Nat} {input : Slice U8} {offset nextOffset : U64}
      {amount : Usize} {before middle after : Environment}
      (positive : 0 < amount.val) (fits : amount.val ≤ input.val.length)
      (advanced : nextOffset.val = offset.val + amount.val)
      (write : pollWrite file input before (some offset) = some (.ok (.Ok amount, file), middle))
      (rest : Chunks file count (input.drop amount, nextOffset) middle after) :
      Chunks file (count + 1) (input, offset) before after

private theorem loop_follows {file : NativeFile} {count : Nat} {input : Cursor}
    {before after : Environment} (plan : Chunks file count input before after)
    (fuel : Nat) (finite : count < fuel) :
    Result.ReadyPrefix (NativeM.loopFuel (iteration file) fuel input)
      before (.ok (.Ok ())) after := by
  induction plan generalizing fuel with
  | empty input offset env done =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [NativeM.loopFuel, empty_step _ _ _ done, Result.ok_bind, NativeM.ok]
      exact .refl _ _
  | @next count input offset nextOffset amount before middle after positive fits advanced write rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold NativeM.loopFuel
      have one := accepted_step file input offset nextOffset amount before middle positive fits advanced write
      have advancedLoop := one.bind (fun result => match result with
        | .cont cursor => NativeM.loopFuel (iteration file) fuel cursor
        | .done reply => NativeM.ok reply)
      simp only [Result.ok_bind] at advancedLoop
      convert advancedLoop.trans (ih fuel (by omega)) using 1
      congr 1
      funext result
      cases result <;> rfl

/-- The standard loop returns success after every positively acknowledged chunk,
within the native loop budget. Its proof uses the actual selected File dictionary. -/
theorem writes_all (file : NativeFile) (input : Slice U8) (offset : U64)
    {count : Nat} {before after : Environment}
    (plan : Chunks file count (input, offset) before after) (finite : count < 262145) :
    Result.ReadyPrefix (io_protocol.io_core.positional.write_all_at file input offset)
      before (.ok (.Ok ())) after := by
  change Result.ReadyPrefix (NativeM.loopFuel (iteration file) 262145 (input, offset))
    before (.ok (.Ok ())) after
  exact loop_follows plan _ finite

theorem caller_order (file : NativeFile) (data : Slice U8) (offset : U64) :
    io_protocol.positional.write_all_and_sync file data offset =
      (io_protocol.io_core.positional.write_all_at file data offset >>= fun result =>
        match result with
        | .Ok () => syncData file
        | .Err error => NativeM.ok (.Err error)) := by
  simp only [io_protocol.positional.write_all_and_sync, monadLift_self]
  apply congrArg (fun next => io_protocol.io_core.positional.write_all_at file data offset >>= next)
  funext result
  cases result with
  | Ok value => cases value; rfl
  | Err error =>
    simp [core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind, NativeM.ok]

/-- The caller requires a complete write before attempting synchronization.
The final native state comes from the independently admitted data sync. -/
theorem synchronizes_after_all (file : NativeFile) (data : Slice U8) (offset : U64)
    {count : Nat} {before middle after : Environment} {reply : Reply}
    (plan : Chunks file count (data, offset) before middle) (finite : count < 262145)
    (sync : pollSync file middle true = some (.ok reply, after)) :
    Result.ReadyPrefix (io_protocol.positional.write_all_and_sync file data offset)
      before (.ok reply) after := by
  rw [caller_order]
  have ready := (writes_all file data offset plan finite).bind fun result =>
    match result with
    | .Ok () => syncData file
    | .Err error => NativeM.ok (.Err error)
  simp only [Result.ok_bind] at ready
  apply ready.trans
  unfold syncData
  exact Result.ReadyPrefix.wait _ _ _ _ _ _ _ sync (.refl _ _)

@[expose] def writeZero : NativeIoError := .staticMessage "WriteZero"
  (NativeFile.bytes (toStr "failed to write whole buffer"))

theorem zero_constant : core.io.error.Error.WRITE_ALL_EOF = Result.ok writeZero := by
  simp [core.io.error.Error.WRITE_ALL_EOF, ExactWrite.Extraction.IoErrorModel.fromStaticMessage,
    ExactWrite.Extraction.IoErrorModel.encodeKind, core.hint.must_use, NativeM.ok, writeZero]

private theorem step_bounds (state : NativeFile.State) (data : Slice U8) (amount : Usize)
    (after : NativeFile.State) (ready : writeStep state data true = some (.Ok amount, after)) :
    amount.val ≤ data.val.length ∧ state.position + amount.val ≤ limit := by
  simp only [writeStep] at ready
  repeat' first | split at ready | simp_all [Option.bind_eq_bind, Option.bind]
  obtain ⟨rfl,rfl⟩ := ready
  constructor <;> simpa [Usize.ofNatCore] using ‹_ ≤ _›

private theorem positional_poll_bounds (file returned : NativeFile) (data : Slice U8)
    (offset : U64) (before after : Environment) (amount : Usize)
    (write : pollWrite file data before (some offset) = some (.ok (.Ok amount, returned), after)) :
    amount.val ≤ data.val.length ∧ offset.val + amount.val ≤ limit := by
  simp only [pollWrite, Option.any, Option.elim, Option.isSome] at write
  repeat' first | split at write | simp_all
  obtain ⟨rfl,rfl⟩ := write.1
  exact step_bounds _ _ _ _ (by assumption)

private theorem poll_write_error (file : NativeFile) (data : Slice U8) (offset : U64)
    (before after : Environment) (exception : Exception)
    (write : pollWrite file data before (some offset) = some (.error exception, after)) :
    exception = .exhausted := by
  simp only [pollWrite] at write
  repeat' first | split at write | simp_all

private theorem kind_no_panic (error : NativeIoError) :
    NativeM.NoPanic (ExactWrite.Extraction.IoErrorModel.kind error) := by
  simp only [ExactWrite.Extraction.IoErrorModel.kind, NativeIoError.kind, Result.nativeGet_bind]
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
    simp only [Result.ofExcept_ok, Result.ok_bind, ExactWrite.Extraction.IoErrorModel.decodeKind]
    split <;> first | exact NativeM.NoPanic.ok _ | exact NativeM.NoPanic.exhausted

theorem step_no_panic (file : NativeFile) (input : Slice U8) (offset : U64) :
    NativeM.NoPanic (iteration file (input, offset)) := by
  simp only [iteration, std.os.unix.fs.FileExt.write_all_at.default_loop.body, monadLift_self,
    core.slice.Slice.is_empty, NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
  split
  · exact .ok _
  · change NativeM.NoPanic (writeAt file input offset >>= _)
    simp only [writeAt, Result.wait_bind]
    apply NativeM.NoPanic.wait
    intro env reply after write
    cases reply with
    | error exception =>
      have equal := poll_write_error file input offset env after exception write
      subst exception
      exact .exhausted
    | ok response =>
      obtain ⟨reply, returned⟩ := response
      cases reply with
      | Ok amount =>
        have ⟨fits, within⟩ := positional_poll_bounds file returned input offset env after amount write
        simp only [Result.ok_bind]
        split
        · simpa only [zero_constant, NativeM.ok, Result.ok_bind] using NativeM.NoPanic.ok
            (.done (.Err writeZero) : ControlFlow Cursor Reply)
        · let next := U64.ofNatCore (offset.val + amount.val) (by
            have bounded : offset.val + amount.val ≤ limit := within
            simp only [limit] at bounded
            scalar_tac)
          have advanced : next.val = offset.val + amount.val := by simp [next]
          simp only [index_suffix input amount fits, checked_advance offset next amount advanced,
            NativeM.fromRust_ok, Result.ok_bind, NativeM.lift, NativeM.ok]
          exact .ok _
      | Err error =>
        simp only [Result.ok_bind, ExactWrite.Extraction.IoErrorModel.isInterrupted,
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
    apply NativeM.NoPanic.bind (step_no_panic file cursor.1 cursor.2)
    intro result
    cases result with
    | cont next => exact ih next
    | done reply => exact .ok reply

private theorem sync_no_panic (file : NativeFile) :
    NativeM.NoPanic (syncData file) := by
  unfold syncData
  apply NativeM.NoPanic.wait
  intro before reply after ready
  cases reply with
  | ok value => exact .ok _
  | error exception =>
    have equal : exception = .exhausted := by
      simp only [pollSync, ↓reduceIte] at ready
      repeat' first | split at ready | simp_all
    subst exception
    exact .exhausted

/-- The actual caller may block or exhaust its verification budget. Every
admitted positive write bounds the slice and cursor advance without a panic. -/
theorem caller_no_panic (file : NativeFile) (input : Slice U8) (offset : U64) :
    NativeM.NoPanic (io_protocol.positional.write_all_and_sync file input offset) := by
  rw [caller_order]
  apply NativeM.NoPanic.bind (loop_no_panic file 262145 (input, offset))
  intro result
  cases result with
  | Ok value => cases value; exact sync_no_panic file
  | Err error => exact .ok _

@[expose] def input : Slice U8 := .from [7#u8, 8#u8] (by scalar_tac)
@[expose] def initial : ByteArray := ⟨#[1, 2]⟩
@[expose] def acceptedPrefix : ByteArray := ⟨#[1, 7]⟩
@[expose] def complete : ByteArray := ⟨#[1, 7, 8]⟩

@[expose] def actionChoice (operation : String) (status : Bool) (value : Nat)
    (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation, .atom (if status then "ok" else "error"),
    .integer value, .bitstring mask 0]) rest

@[expose] def shortWrite (rest : Term) : Term := actionChoice "write_at" true 1 ⟨#[0, 0]⟩ rest
@[expose] def sync : Term := actionChoice "sync_data" true 0 ByteArray.empty .nil

@[expose] def world (script : Term) (classification : Option String := none) : Environment :=
  { nativeRefCounter := 3
    nativeHeap := [(1, typeName, encode ⟨initial, initial, 5, script⟩)] ++
      match classification with
      | none => []
      | some kind => [(2, NativeIoError.typeName, .atom "live"),
          (3, NativeIoError.kindTypeName, NativeIoError.kindEntry (.os 2) kind)] }

@[expose] def replyTerm : Reply → Term
  | .Ok () => .atom "ok"
  | .Err (.staticMessage kind _) => .atom kind
  | .Err (.os code) => .integer code
  | .Err (.simple kind) => .tuple #[.atom "simple", .atom kind]

@[expose] def reportReply (native : NativeM Reply) : Result Term := do
  let reply ← native
  Result.ok (replyTerm reply)

@[expose] def written (reply : Term) (visible durable : ByteArray)
    (remaining : Term) (hasError : Bool) (cfg : Concurrent.Config Term) : Bool :=
  let env := match cfg with
    | .start env .. => env
    | .running state .. => state.nativeView []
  match cfg.outcome, NativeFile.lookup ⟨1⟩ env with
  | .ok actual, some file =>
    actual.identical reply && file.visible.data == visible.data && file.durable.data == durable.data &&
      file.position == 5 && file.script.identical remaining &&
      env.nativeHeap.any (fun cell => cell.1 == 2 && cell.2.1 == NativeIoError.typeName) == hasError
  | _, _ => false

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem two_short_writes_synchronize (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (written (.atom "ok") complete complete .nil false) 32
      (.start (world (shortWrite (shortWrite sync))) (reportReply
        (io_protocol.positional.write_all_and_sync ⟨1⟩ input 1#u64)) elapsed) = true := by
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem write_zero_preserves_prefix (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (written (.atom "WriteZero") acceptedPrefix initial sync false) 32
      (.start (world (shortWrite (actionChoice "write_at" true 0 ⟨#[0, 0]⟩ sync))) (reportReply
        (io_protocol.positional.write_all_and_sync ⟨1⟩ input 1#u64)) elapsed) = true := by
  rw [caller_order]
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem interrupted_write_retries_same_range (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (written (.atom "ok") complete complete .nil false) 32
      (.start (world (shortWrite (actionChoice "write_at" false 2 ⟨#[0, 0]⟩
        (shortWrite sync))) (some "Interrupted")) (reportReply
        (io_protocol.positional.write_all_and_sync ⟨1⟩ input 1#u64)) elapsed) = true := by
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem fatal_write_preserves_prefix (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (written (.integer 2) acceptedPrefix initial sync true) 32
      (.start (world (shortWrite (actionChoice "write_at" false 2 ⟨#[0, 0]⟩ sync))
        (some "InputOutputError")) (reportReply
        (io_protocol.positional.write_all_and_sync ⟨1⟩ input 1#u64)) elapsed) = true := by
  rw [caller_order]
  cbv

set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem sync_error_after_complete_write (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (written (.integer 2) complete acceptedPrefix .nil true) 32
      (.start (world (shortWrite (shortWrite (actionChoice "sync_data" false 2 ⟨#[0, 1]⟩ .nil)))
        (some "InputOutputError")) (reportReply
        (io_protocol.positional.write_all_and_sync ⟨1⟩ input 1#u64)) elapsed) = true := by
  cbv

end ExactWrite.Properties
