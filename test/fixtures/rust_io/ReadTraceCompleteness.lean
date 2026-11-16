module
public import GuardedRecovery.ReadTrace
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.ReadCompleteness
open GuardedRecovery.ReadTrace

private theorem readBuffer_zero (state : NativeFile.State) (buffer : Slice U8)
    (bounded : 0 ≤ buffer.val.length) (available : 0 ≤ state.visible.size - state.position) :
    NativeFile.readBuffer state buffer 0 bounded available = buffer := by
  apply Slice.ext
  simp [NativeFile.readBuffer]

private theorem readBuffer_length (state : NativeFile.State) (buffer : Slice U8) (count : Nat)
    (bounded : count ≤ buffer.val.length) (available : count ≤ state.visible.size - state.position) :
    (NativeFile.readBuffer state buffer count bounded available).val.length = buffer.val.length := by
  have size : (state.visible.data.toList.drop state.position |>.take count).length = count := by
    simp only [List.length_take,List.length_drop,Array.length_toList]
    simp only [← ByteArray.size_data] at available
    omega
  simp [NativeFile.readBuffer]
  omega

private theorem slice_one (buffer : Slice U8) (length : buffer.val.length = 1) :
    ∃ byte, buffer = one byte := by
  cases values : buffer.val with
  | nil => simp [values] at length
  | cons byte tail =>
    cases tail with
    | nil =>
      refine ⟨byte,?_⟩
      apply Slice.ext
      simp [one,values]
    | cons other rest => simp [values] at length

/-- A successful one-byte model read has only error, EOF or exactly one-byte
outcomes. Invalid, oversized and blocked choices cannot fabricate another case. -/
theorem readStep_cases (state after : NativeFile.State)
    (reply : core.result.Result Usize NativeIoError) (updated : Slice U8)
    (step : NativeFile.readStep state (one 0#u8) = some (reply,after,updated)) :
    (∃ error, reply = .Err error ∧ updated = one 0#u8) ∨
    (reply = .Ok 0#usize ∧ updated = one 0#u8) ∨
    ∃ byte, reply = .Ok 1#usize ∧ updated = one byte := by
  unfold NativeFile.readStep at step
  split at step
  · contradiction
  · cases chosen : NativeFile.action "read" state.script with
    | none => simp [chosen] at step
    | some choice =>
      obtain ⟨success,count,mask,rest⟩ := choice
      simp only [chosen,Option.bind_eq_bind,Option.bind_some] at step
      cases durable : NativeFile.persist state.durable state.visible mask with
      | none => simp [durable] at step
      | some data =>
        simp only [durable,Option.bind_some] at step
        cases success
        · simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at step
          obtain ⟨rfl,rfl,rfl⟩ := step
          exact .inl ⟨_,rfl,rfl⟩
        · simp only [↓reduceIte] at step
          split at step
          · rename_i bounded
            split at step
            · rename_i available
              split at step
              · contradiction
              · simp only [Option.some.injEq,Prod.mk.injEq] at step
                obtain ⟨rfl,rfl,rfl⟩ := step
                have small : count ≤ 1 := by simpa [one] using bounded
                rcases Nat.le_one_iff_eq_zero_or_eq_one.mp small with rfl | rfl
                · exact .inr (.inl ⟨rfl,readBuffer_zero _ _ _ _⟩)
                · obtain ⟨byte,equal⟩ := slice_one
                    (NativeFile.readBuffer state (one 0#u8) 1 bounded available)
                    (by simpa [one] using readBuffer_length state (one 0#u8) 1 bounded available)
                  exact .inr (.inr ⟨byte,rfl,equal⟩)
            · contradiction
          · contradiction

theorem pollRead_cases (file returnedFile : NativeFile) (before after : Environment)
    (reply : core.result.Result Usize NativeIoError) (updated : Slice U8)
    (ready : NativeFile.pollRead file (one 0#u8) before =
      some (.ok (reply,returnedFile,updated),after)) :
    returnedFile = file ∧
      ((∃ error, reply = .Err error ∧ updated = one 0#u8) ∨
       (reply = .Ok 0#usize ∧ updated = one 0#u8) ∨
       ∃ byte, reply = .Ok 1#usize ∧ updated = one byte) := by
  unfold NativeFile.pollRead at ready
  cases lookup : NativeFile.lookup file before with
  | none => simp [lookup] at ready
  | some state =>
    simp only [lookup] at ready
    split at ready
    · contradiction
    · cases step : NativeFile.readStep state (one 0#u8) with
      | none => simp [step] at ready
      | some result =>
        obtain ⟨readReply,stored,buffer⟩ := result
        simp only [step,Option.some.injEq,Prod.mk.injEq,Except.ok.injEq] at ready
        obtain ⟨⟨rfl,rfl,rfl⟩,rfl⟩ := ready
        exact ⟨rfl,readStep_cases _ _ _ _ step⟩

private theorem read_once_returns {file returnedFile : NativeFile} {before after : Environment}
    {reply : core.result.Result Usize NativeIoError} {updated : Slice U8}
    (trace : Result.ReadyPrefix (io_core.read_once file (one 0#u8)) before
      (.ok (reply,returnedFile,updated)) after) :
    NativeFile.pollRead file (one 0#u8) before = some (.ok (reply,returnedFile,updated),after) := by
  simp only [io_core.read_once,monadLift_self,NativeFile.read] at trace
  obtain ⟨response,middle,poll,rest⟩ := trace.wait_returns
  cases response with
  | error exception => cases rest
  | ok returned =>
    obtain ⟨rfl,rfl⟩ := rest.ok_returns
    exact poll

private theorem finish_reads {file returnedFile : NativeFile}
    {initial before after : Environment}
    {expected reply : core.result.Result (Option U16) NativeIoError}
    (accepted : Reads file initial expected before)
    (trace : Result.ReadyPrefix (NativeM.ok (expected,file)) before (.ok (reply,returnedFile)) after) :
    returnedFile = file ∧ Reads file initial reply after := by
  simp only [NativeM.ok] at trace
  obtain ⟨values,states⟩ := trace.ok_returns
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj values
  cases states
  exact ⟨rfl,accepted⟩

/-- Every completed execution of the actual parser belongs to the admitted read
relation. The proof needs no assumed valid state or successful IO premise. -/
theorem reads_complete {file returnedFile : NativeFile} {before after : Environment}
    {reply : core.result.Result (Option U16) NativeIoError}
    (trace : Result.ReadyPrefix (read_word file) before (.ok (reply,returnedFile)) after) :
    returnedFile = file ∧ Reads file before reply after := by
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val] at trace
  obtain ⟨⟨firstReply,firstFile,firstBuffer⟩,middle,firstRead,rest⟩ := trace.bind_returns
  have pollFirst := read_once_returns firstRead
  obtain ⟨rfl,choices⟩ := pollRead_cases _ _ _ _ _ _ pollFirst
  rcases choices with ⟨error,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨low,rfl,rfl⟩
  · exact finish_reads (.firstError error pollFirst) rest
  · exact finish_reads (.firstEof pollFirst) rest
  · simp only [UScalar.ofNatCore_val_eq] at rest
    obtain ⟨⟨secondReply,secondFile,secondBuffer⟩,readAfter,secondRead,last⟩ := rest.bind_returns
    have pollSecond := read_once_returns secondRead
    obtain ⟨rfl,choices⟩ := pollRead_cases _ _ _ _ _ _ pollSecond
    rcases choices with ⟨error,rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨high,rfl,rfl⟩
    · exact finish_reads (.secondError low error pollFirst pollSecond) last
    · exact finish_reads (.secondEof low pollFirst pollSecond) last
    · apply finish_reads (.complete low high pollFirst pollSecond)
      simpa [NativeM.ok,Array.from_slice,Array.index_usize,one,
        NativeM.monadLift_eq,NativeM.fromRust,word,Result.ok_bind] using last

/-- The admitted relation characterizes completed parser executions in both
directions, including Rust errors and exact final states. -/
theorem completed_iff (file returnedFile : NativeFile) (before after : Environment)
    (reply : core.result.Result (Option U16) NativeIoError) :
    Result.ReadyPrefix (read_word file) before (.ok (reply,returnedFile)) after ↔
      returnedFile = file ∧ Reads file before reply after := by
  constructor
  · exact reads_complete
  · rintro ⟨rfl,trace⟩
    exact trace.ready

end GuardedRecovery.ReadCompleteness
