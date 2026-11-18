module
public import ExactRead.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace ExactRead.Properties

@[expose] def empty : Slice U8 := .from [] (by scalar_tac)
@[expose] def two : Slice U8 := .from [0#u8,0#u8] (by scalar_tac)
@[expose] def eofError : NativeIoError := .staticMessage "UnexpectedEof"
  (NativeFile.bytes (toStr "failed to fill whole buffer"))

theorem eof_constant : core.io.error.Error.READ_EXACT_EOF = Result.ok eofError := by
  simp [core.io.error.Error.READ_EXACT_EOF,ExactRead.Extraction.IoErrorModel.fromStaticMessage,
    ExactRead.Extraction.IoErrorModel.encodeKind,core.hint.must_use,NativeM.ok,eofError]

theorem empty_input (file : NativeFile) (env : Environment) :
    (io_core.fill_exact file empty).run env [] = (.ok (.Ok (),file,empty),env) := by
  cbv
  simp only [Result.ok_apply]


/-- EOF is the actual std constant, preserving the buffer returned by read. -/
theorem eof_contract (file returned : NativeFile) (buffer updated : Slice U8)
    (before after : Environment)
    (nonempty : core.slice.Slice.is_empty buffer = RustM.ok false)
    (remaining : core.slice.Slice.is_empty updated = RustM.ok false)
    (read : NativeFile.pollRead file buffer before =
      some (.ok (.Ok 0#usize,returned,updated),after)) :
    Result.ReadyPrefix (io_core.fill_exact file buffer) before
      (.ok (.Err eofError,returned,updated)) after := by
  simp only [io_core.fill_exact,alloc.io.read.Read.read_exact.default,
    alloc.io.read.default_read_exact,alloc.io.read.default_read_exact_loop,
    NativeM.loop,monadLift_self]
  rw [NativeM.loopFuel]
  simp only [alloc.io.read.default_read_exact_loop.body,nonempty,NativeM.fromRust_ok,
    NativeM.monadLift_eq,Result.ok_bind,Bool.false_eq_true,↓reduceIte]
  simp only [monadLift_self,bind_assoc]
  change Result.ReadyPrefix (NativeFile.read file buffer >>= _) _ _ _
  simp only [NativeFile.read,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ read
  simp only [Result.ok_bind,remaining,NativeM.monadLift_eq,NativeM.fromRust_ok,
    Bool.false_eq_true,↓reduceIte, eof_constant,NativeM.ok]
  exact Result.ReadyPrefix.refl _ _

@[expose] def action (count : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom "read",.atom "ok",.integer count,.bitstring ByteArray.empty 0]) rest
@[expose] def world (script : Term) : Environment := {
  nativeRefCounter := 1
  nativeHeap := [(1,NativeFile.typeName,NativeFile.encode ⟨ByteArray.empty,ByteArray.empty,0,script⟩)] }

theorem eof_input :
    (io_core.fill_exact ⟨1⟩ two).run (world (action 0 .nil)) [] =
      (.ok (.Err eofError,⟨1⟩,two),world .nil) := by
  cbv
  rw [Result.wait_ready_run _ _ _ (world .nil) (.ok (.Ok 0#usize,⟨1⟩,two)) (by cbv)]
  cbv
  simp only [Result.ok_apply]

@[expose] def actionWith (count : Nat) (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom "read",.atom "ok",.integer count,.bitstring mask 0]) rest

@[expose] def worldBytes (bytes : ByteArray) (position : Nat) (script : Term) : Environment := {
  nativeRefCounter := 1
  nativeHeap := [(1,NativeFile.typeName,NativeFile.encode ⟨bytes,bytes,position,script⟩)] }
@[expose] def prefixBuffer : Slice U8 := .from [7#u8,0#u8] (by scalar_tac)
@[expose] def complete : Slice U8 := .from [7#u8,8#u8] (by scalar_tac)

theorem partial_eof :
    (io_core.fill_exact ⟨1⟩ two).run (worldBytes ⟨#[7]⟩ 0 (actionWith 1 ⟨#[0]⟩ (actionWith 0 ⟨#[0]⟩ .nil))) [] =
      (.ok (.Err eofError,⟨1⟩,prefixBuffer),worldBytes ⟨#[7]⟩ 1 .nil) := by
  cbv
  rw [Result.wait_ready_run _ _ _ (worldBytes ⟨#[7]⟩ 1 (actionWith 0 ⟨#[0]⟩ .nil))
    (.ok (.Ok 1#usize,⟨1⟩,prefixBuffer)) (by cbv)]
  cbv
  rw [Result.wait_ready_run _ _ _ (worldBytes ⟨#[7]⟩ 1 .nil)
    (.ok (.Ok 0#usize,⟨1⟩,(Slice.from [0#u8] (by scalar_tac)))) (by cbv)]
  cbv
  simp only [Result.ok_apply]

theorem complete_read :
    (io_core.fill_exact ⟨1⟩ two).run (worldBytes ⟨#[7,8]⟩ 0 (actionWith 2 ⟨#[0,0]⟩ .nil)) [] =
      (.ok (.Ok (),⟨1⟩,complete),worldBytes ⟨#[7,8]⟩ 2 .nil) := by
  cbv
  rw [Result.wait_ready_run _ _ _ (worldBytes ⟨#[7,8]⟩ 2 .nil)
    (.ok (.Ok 2#usize,⟨1⟩,complete)) (by cbv)]
  cbv
  simp only [Result.ok_apply]

@[expose] def errorAction (rest : Term) : Term := .cons
  (.tuple #[.atom "read",.atom "error",.integer 1,.bitstring ByteArray.empty 0]) rest
@[expose] def errorWorld (label : String) (live : Bool) (script : Term) : Environment := {
  nativeRefCounter := 3
  nativeHeap := [(3,NativeFile.typeName,NativeFile.encode ⟨ByteArray.empty,ByteArray.empty,0,script⟩)] ++
    (if live then [(1,NativeIoError.typeName,.atom "live")] else []) ++
    [(2,NativeIoError.kindTypeName,NativeIoError.kindEntry (.os 1) label)] }

theorem interrupted_retry :
    (io_core.fill_exact ⟨3⟩ two).run
      (errorWorld "Interrupted" true (errorAction (action 0 .nil))) [] =
      (.ok (.Err eofError,⟨3⟩,two),errorWorld "Interrupted" false .nil) := by
  cbv
  rw [Result.wait_ready_run _ _ _ (errorWorld "Interrupted" true (action 0 .nil))
    (.ok (.Err (.os 1),⟨3⟩,two)) (by cbv)]
  cbv
  simp only [Result.nativeGet_continuation_run]
  cbv
  rw [Result.wait_ready_run _ _ _ (errorWorld "Interrupted" false (action 0 .nil))
    (.ok ()) (by cbv)]
  cbv
  rw [Result.wait_ready_run _ _ _ (errorWorld "Interrupted" false .nil)
    (.ok (.Ok 0#usize,⟨3⟩,two)) (by cbv)]
  cbv
  simp only [Result.ok_apply]

theorem other_error :
    (io_core.fill_exact ⟨3⟩ two).run
      (errorWorld "InputOutputError" true (errorAction .nil)) [] =
      (.ok (.Err (.os 1),⟨3⟩,two),errorWorld "InputOutputError" true .nil) := by
  cbv
  rw [Result.wait_ready_run _ _ _ (errorWorld "InputOutputError" true .nil)
    (.ok (.Err (.os 1),⟨3⟩,two)) (by cbv)]
  cbv
  simp only [Result.nativeGet_continuation_run]
  cbv
  simp only [Result.ok_apply]

/-- The complete-read trace can be reused by an arbitrary first-party caller. -/
theorem complete_prefix :
    Result.ReadyPrefix (io_core.fill_exact ⟨1⟩ two)
      (worldBytes ⟨#[7,8]⟩ 0 (actionWith 2 ⟨#[0,0]⟩ .nil))
      (.ok (.Ok (),⟨1⟩,complete)) (worldBytes ⟨#[7,8]⟩ 2 .nil) := by
  cbv
  apply Result.ReadyPrefix.wait _ _ (.ok (.Ok 2#usize,⟨1⟩,complete)) _
    (worldBytes ⟨#[7,8]⟩ 2 .nil) _ _ (by cbv)
  cbv
  exact .refl _ _

theorem word_complete :
    Result.ReadyPrefix (io_core.exact_word ⟨1⟩)
      (worldBytes ⟨#[7,8]⟩ 0 (actionWith 2 ⟨#[0,0]⟩ .nil))
      (.ok (.Ok 2055#u16,⟨1⟩)) (worldBytes ⟨#[7,8]⟩ 2 .nil) := by
  simp only [io_core.exact_word,monadLift_self,NativeM.lift,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change Result.ReadyPrefix (io_core.fill_exact ⟨1⟩ two >>= _) _ _ _
  refine (complete_prefix.bind _).trans ?_
  cbv
  exact .refl _ _

theorem caller_complete :
    Result.ReadyPrefix (optional_exact_word ⟨1⟩)
      (worldBytes ⟨#[7,8]⟩ 0 (actionWith 2 ⟨#[0,0]⟩ .nil))
      (.ok (.Ok (some 2055#u16),⟨1⟩)) (worldBytes ⟨#[7,8]⟩ 2 .nil) := by
  simp only [optional_exact_word,monadLift_self]
  refine (word_complete.bind _).trans ?_
  cbv
  exact .refl _ _

theorem eof_prefix :
    Result.ReadyPrefix (io_core.fill_exact ⟨1⟩ two)
      (world (action 0 .nil)) (.ok (.Err eofError,⟨1⟩,two)) (world .nil) := by
  exact eof_contract _ _ _ _ _ _ (by cbv) (by cbv) (by cbv)

theorem word_eof :
    Result.ReadyPrefix (io_core.exact_word ⟨1⟩) (world (action 0 .nil))
      (.ok (.Err eofError,⟨1⟩)) (world .nil) := by
  simp only [io_core.exact_word,monadLift_self,NativeM.lift,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change Result.ReadyPrefix (io_core.fill_exact ⟨1⟩ two >>= _) _ _ _
  refine (eof_prefix.bind _).trans ?_
  cbv
  exact .refl _ _

theorem caller_eof :
    Result.ReadyPrefix (optional_exact_word ⟨1⟩) (world (action 0 .nil))
      (.ok (.Ok none,⟨1⟩)) (world .nil) := by
  simp only [optional_exact_word,monadLift_self]
  refine (word_eof.bind _).trans ?_
  cbv
  apply Result.ReadyPrefix.nativeGet
  cbv
  exact .refl _ _

@[expose] def truncatedKind : core.io.error.ErrorKind → Bool
  | .UnexpectedEof => true
  | _ => false

theorem kind_eq (kind : core.io.error.ErrorKind) :
    core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq kind .UnexpectedEof =
      Result.ok (truncatedKind kind) := by
  cases kind <;> simp [core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq,
    truncatedKind,core.io.error.ErrorKind.read_discriminant,NativeM.lift,NativeM.ok]

/-- The modeled read retains the initialized slice length. -/
theorem read_buffer_length (state : NativeFile.State) (buffer : Slice U8) (count : Nat)
    (bounded : count ≤ buffer.val.length)
    (available : count ≤ state.visible.size - state.position) :
    (NativeFile.readBuffer state buffer count bounded available).val.length = buffer.val.length := by
  have length : (state.visible.data.toList.drop state.position |>.take count).length = count := by
    simp only [List.length_take,List.length_drop,Array.length_toList]
    simp only [← ByteArray.size_data] at available
    omega
  simp only [NativeFile.readBuffer,Slice.from_val,List.length_append,List.length_map,
    length,List.length_drop]
  omega

theorem read_step_bounds (state next : NativeFile.State) (buffer updated : Slice U8)
    (count : Usize)
    (step : NativeFile.readStep state buffer = some (.Ok count,next,updated)) :
    count.val ≤ updated.val.length := by
  simp only [NativeFile.readStep] at step
  repeat' first | split at step | simp_all [Option.bind_eq_bind,Option.bind,read_buffer_length]
  obtain ⟨rfl,rfl,rfl⟩ := step
  simp only [read_buffer_length]
  assumption

theorem kind_no_panic (error : NativeIoError) :
    NativeM.NoPanic (ExactRead.Extraction.IoErrorModel.kind error) := by
  simp only [ExactRead.Extraction.IoErrorModel.kind,NativeIoError.kind,
    Result.nativeGet_bind]
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
    simp only [Result.ofExcept_ok,Result.ok_bind,ExactRead.Extraction.IoErrorModel.decodeKind]
    split <;> first | exact NativeM.NoPanic.ok _ | exact NativeM.NoPanic.exhausted

theorem read_poll_bounds (file returned : NativeFile) (buffer updated : Slice U8)
    (before after : Environment) (count : Usize)
    (read : NativeFile.pollRead file buffer before = some (.ok (.Ok count,returned,updated),after)) :
    count.val ≤ updated.val.length := by
  cases found : NativeFile.lookup file before with
  | none => simp [NativeFile.pollRead, found] at read
  | some state =>
    cases blocked : NativeFile.blocked state with
    | true => simp [NativeFile.pollRead, found, blocked] at read
    | false =>
      cases step : NativeFile.readStep state buffer with
      | none => simp [NativeFile.pollRead, found, blocked, step] at read
      | some reply =>
        obtain ⟨result, next, slice⟩ := reply
        simp [NativeFile.pollRead, found, blocked, step] at read
        rw [← read.2.2.1]
        rw [read.1] at step
        exact read_step_bounds _ _ _ _ _ step

theorem read_poll_error (file : NativeFile) (buffer : Slice U8)
    (before after : Environment) (exception : Exception)
    (read : NativeFile.pollRead file buffer before = some (.error exception,after)) :
    exception = .exhausted := by
  simp only [NativeFile.pollRead] at read
  repeat' first | split at read | simp_all

theorem exact_step_no_panic (back : Slice U8 → Slice U8) (file : NativeFile) (buffer : Slice U8) :
    NativeM.NoPanic (alloc.io.read.default_read_exact_loop.body
      std.fs.File.Insts.AllocIoReadRead back file buffer) := by
  simp only [alloc.io.read.default_read_exact_loop.body,core.slice.Slice.is_empty,
    NativeM.monadLift_eq,NativeM.fromRust_ok,Result.ok_bind,monadLift_self]
  split
  · simp_all only [↓reduceIte,NativeM.ok]
    exact .ok _
  · simp only [NativeFile.read,Result.wait_bind]
    apply NativeM.NoPanic.wait
    intro env reply after read
    cases reply with
    | error exception =>
      have equal := read_poll_error file buffer env after exception read
      subst exception
      exact .exhausted
    | ok response =>
      obtain ⟨reply,returned,updated⟩ := response
      cases reply with
      | Ok count =>
        simp only [Result.ok_bind]
        split
        · split
          · exact .ok _
          · simp only [eof_constant,NativeM.ok,Result.ok_bind]
            exact .ok _
        · have bounded := read_poll_bounds file returned buffer updated env after count read
          simp only [core.slice.index.Slice.index_mut,
            core.slice.index.SliceIndexRangeFromUsizeSlice.index_mut]
          simp only [Slice.length] at *
          simp [bounded,NativeM.monadLift_eq,NativeM.fromRust_ok,NativeM.ok]
          exact .ok _
      | Err error =>
        simp only [Result.ok_bind,ExactRead.Extraction.IoErrorModel.isInterrupted,monadLift_self,bind_assoc]
        apply NativeM.NoPanic.bind (kind_no_panic error)
        intro kind
        cases kind <;> simp only [NativeM.ok,Result.ok_bind,↓reduceIte]
        all_goals first
          | exact .ok _
          | exact (NativeM.NoPanic.io_error_dispose error).bind _ (fun _ => .ok _)

theorem exact_loop_no_panic (fuel : Nat) (back : Slice U8 → Slice U8)
    (file : NativeFile) (buffer : Slice U8) :
    NativeM.NoPanic (NativeM.loopFuel
      (fun (back,file,buffer) => alloc.io.read.default_read_exact_loop.body
        std.fs.File.Insts.AllocIoReadRead back file buffer) fuel (back,file,buffer)) := by
  induction fuel generalizing back file buffer with
  | zero => exact .exhausted
  | succ fuel ih =>
    rw [NativeM.loopFuel]
    apply NativeM.NoPanic.bind (exact_step_no_panic back file buffer)
    intro control
    cases control with
    | done value => exact .ok value
    | cont state =>
      obtain ⟨back,file,buffer⟩ := state
      exact ih back file buffer

/-- A certificate for the actual File-specific implementation, under every model environment. -/
theorem fill_no_panic (file : NativeFile) (buffer : Slice U8) :
    NativeM.NoPanic (io_core.fill_exact file buffer) := by
  simp only [io_core.fill_exact,alloc.io.read.Read.read_exact.default,
    alloc.io.read.default_read_exact,alloc.io.read.default_read_exact_loop,
    NativeM.loop,monadLift_self]
  exact exact_loop_no_panic _ _ _ _

end ExactRead.Properties
