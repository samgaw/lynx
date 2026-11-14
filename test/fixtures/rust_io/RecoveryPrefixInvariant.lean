module
public import Record.AppendPrefixInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RecoveryPrefixInvariant
variable [heapLayout : Record.Properties.HeapLayout]
open NativeFile Record.Properties Record.ReadProperties Record.ResizeProperties
  Record.RepairCrashProperties Record.AppendPrefixInvariant Record.EncodedPrefixRecovery

omit heapLayout in
private theorem read_step_preserves (before : State) (buffer : Slice U8)
    (reply : core.result.Result Usize NativeIoError) (after : State) (updated : Slice U8)
    (head : ByteArray) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (step : readStep before buffer = some (reply, after, updated)) :
    Admitted after ∧ Prefix head after.visible ∧ Prefix head after.durable := by
  unfold readStep at step
  split at step
  · contradiction
  · cases chosen : action "read" before.script with
    | none => simp [chosen] at step
    | some choice =>
        obtain ⟨success, count, mask, rest⟩ := choice
        simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
        cases accepted : persist before.durable before.visible mask with
        | none => simp [accepted] at step
        | some data =>
            simp only [accepted, Option.bind_some] at step
            have sizes := persist_lengths _ _ _ _ accepted
            have image := persist_prefix _ _ _ _ _ durable visible accepted
            cases success
            · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at step
              obtain ⟨rfl, rfl, rfl⟩ := step
              exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega, valid.2.2⟩,
                visible, image⟩
            · simp only [↓reduceIte] at step
              split at step
              · split at step
                · split at step
                  · contradiction
                  · simp only [Option.some.injEq, Prod.mk.injEq] at step
                    obtain ⟨rfl, rfl, rfl⟩ := step
                    exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega,
                        by dsimp; have := valid.1; have := valid.2.2; omega⟩, visible, image⟩
                · contradiction
              · contradiction



omit heapLayout in
private theorem seek_step_preserves (before : State) (origin : SeekFrom)
    (reply : core.result.Result U64 NativeIoError) (after : State)
    (head : ByteArray) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (step : seekStep before origin = some (reply, after)) :
    Admitted after ∧ Prefix head after.visible ∧ Prefix head after.durable := by
  unfold seekStep at step
  cases chosen : action "seek" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, count, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases accepted : persist before.durable before.visible mask with
      | none => simp [accepted] at step
      | some data =>
          simp only [accepted, Option.bind_some] at step
          have sizes := persist_lengths _ _ _ _ accepted
          have image := persist_prefix _ _ _ _ _ durable visible accepted
          cases success
          · simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at step
            obtain ⟨rfl, rfl⟩ := step
            exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega, valid.2.2⟩,
              visible, image⟩
          · simp only [↓reduceIte] at step
            split at step
            · contradiction
            · simp only [Option.some.injEq, Prod.mk.injEq] at step
              obtain ⟨rfl, rfl⟩ := step
              exact ⟨⟨valid.1, by dsimp; have := valid.1; have := valid.2.1; omega,
                by dsimp; omega⟩, visible, image⟩

private theorem seek_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (next : core.result.Result U64 NativeIoError × NativeFile → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (continuation : ∀ reply after, Admitted after → Prefix head after.visible →
      Prefix head after.durable →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply, file))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (io_core.seek_to file 0#u64 >>= next) (fileEnv env file before frame) := by
  have initial : PrefixInvariant env file frame head (fileEnv env file before frame) :=
    ⟨before, rfl, valid, visible, durable⟩
  simp only [io_core.seek_to, io_core.seek_from, Record.Extraction.FileModel.seek,
    NativeFile.seek, monadLift_self, Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro actual world ready
  unfold pollSeek at ready
  rw [lookup_admitted env file before frame separate valid] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases step : seekStep before (.start 0#u64) with
    | none =>
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        simpa only [Result.error_bind] using
          Result.NativeInvariant.error (PrefixInvariant env file frame head) .exhausted _ initial
    | some outcome =>
        obtain ⟨reply, after⟩ := outcome
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        rw [store_at env file before after frame separate]
        simp only [Result.ok_bind]
        have kept := seek_step_preserves before _ reply after head valid visible durable step
        exact continuation reply after kept.1 kept.2.1 kept.2.2

private theorem read_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (buffer : Slice U8) (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (continuation : ∀ reply buffer after, Admitted after → Prefix head after.visible →
      Prefix head after.durable →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply, file, buffer))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (io_core.read_once file buffer >>= next) (fileEnv env file before frame) := by
  have initial : PrefixInvariant env file frame head (fileEnv env file before frame) :=
    ⟨before, rfl, valid, visible, durable⟩
  simp only [io_core.read_once, monadLift_self, NativeFile.read, Result.wait_bind]
  apply Result.NativeInvariant.wait _ _ _ initial
  intro actual world ready
  unfold pollRead at ready
  rw [lookup_admitted env file before frame separate valid] at ready
  by_cases stopped : blocked before = true
  · simp [stopped] at ready
  · simp only [stopped] at ready
    cases step : readStep before buffer with
    | none =>
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        simpa only [Result.error_bind] using
          Result.NativeInvariant.error (PrefixInvariant env file frame head) .exhausted _ initial
    | some outcome =>
        obtain ⟨reply, after, updated⟩ := outcome
        simp only [step] at ready
        obtain ⟨rfl, rfl⟩ := ready
        rw [store_at env file before after frame separate]
        simp only [Result.ok_bind]
        have kept := read_step_preserves before buffer reply after updated head valid visible durable step
        exact continuation reply updated after kept.1 kept.2.1 kept.2.2

omit heapLayout in
private theorem from_rust_invariant (holds : Environment → Prop) (before : Environment)
    (valid : holds before) (computation : RustM α) (next : α → NativeM β)
    (continuation : ∀ value, Result.NativeInvariant holds (next value) before) :
    Result.NativeInvariant holds (NativeM.fromRust computation >>= next) before := by
  unfold NativeM.fromRust
  split
  · simp only [Result.ok_bind]
    apply continuation
  · simp only [NativeM.fail, Result.error_bind]
    exact Result.NativeInvariant.error _ _ _ valid
  · simp only [Result.error_bind]
    exact Result.NativeInvariant.error _ _ _ valid


private theorem word_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (continuation : ∀ reply after, Admitted after → Prefix head after.visible →
      Prefix head after.durable →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply, file))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (read_word file >>= next) (fileEnv env file before frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind, bind_assoc]
  apply read_next_invariant env file frame head before _ _ separate valid visible durable
  intro first buffer middle admitted firstVisible firstDurable
  cases first with
  | Err error =>
      simp only [NativeM.ok, Result.ok_bind]
      exact continuation (.Err error) _ admitted firstVisible firstDurable
  | Ok count =>
      cases position : count.val with
      | zero =>
          simp only [position, NativeM.ok, Result.ok_bind]
          exact continuation (.Ok none) _ admitted firstVisible firstDurable
      | succ count =>
          simp only [position, bind_assoc]
          apply read_next_invariant env file frame head middle _ _ separate admitted firstVisible firstDurable
          intro second buffer2 after finalValid finalVisible finalDurable
          cases second with
          | Err error =>
              simp only [NativeM.ok, Result.ok_bind]
              exact continuation (.Err error) _ finalValid finalVisible finalDurable
          | Ok count =>
              cases position2 : count.val with
              | zero =>
                  simp only [position2, NativeM.ok, Result.ok_bind]
                  exact continuation (.Ok none) _ finalValid finalVisible finalDurable
              | succ count =>
                  simp only [position2, NativeM.monadLift_eq, bind_assoc]
                  apply from_rust_invariant _ _ ⟨after, rfl, finalValid, finalVisible, finalDurable⟩
                  intro low
                  apply from_rust_invariant _ _ ⟨after, rfl, finalValid, finalVisible, finalDurable⟩
                  intro high
                  simp only [NativeM.ok, Result.ok_bind]
                  exact continuation _ _ finalValid finalVisible finalDurable


private theorem record_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (continuation : ∀ reply after, Admitted after → Prefix head after.visible →
      Prefix head after.durable →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply, file))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (read_record file >>= next) (fileEnv env file before frame) := by
  simp only [read_record, monadLift_self, bind_assoc]
  apply word_next_invariant env file frame head before _ separate valid visible durable
  intro first middle admitted v d
  cases first with
  | Err error =>
      simpa only [NativeM.ok, monadLift_self, Result.ok_bind] using continuation (.Err error) middle admitted v d
  | Ok option =>
      cases option with
      | none =>
          simpa only [NativeM.ok, monadLift_self, Result.ok_bind] using continuation (.Ok none) middle admitted v d
      | some value =>
          simp only [bind_assoc]
          apply word_next_invariant env file frame head middle _ separate admitted v d
          intro second after admitted v d
          cases second with
          | Err error =>
              simpa only [NativeM.ok, monadLift_self, Result.ok_bind] using continuation (.Err error) after admitted v d
          | Ok option =>
              cases option with
              | none =>
                  simpa only [NativeM.ok, monadLift_self, Result.ok_bind] using continuation (.Ok none) after admitted v d
              | some inverse =>
                  simp only [io_core.decode_record, NativeM.lift, NativeM.ok, monadLift_self,
                    Result.ok_bind, bind_assoc]
                  split <;> simp only [Result.ok_bind] <;> exact continuation _ _ admitted v d


private theorem loop_next_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (accumulated : alloc.vec.Vec U16) (maxRecords : Usize) (fuel : Nat)
    (next : core.result.Result (alloc.vec.Vec U16) NativeIoError × NativeFile → NativeM α)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable)
    (continuation : ∀ reply after, Admitted after → Prefix head after.visible →
      Prefix head after.durable →
      Result.NativeInvariant (PrefixInvariant env file frame head) (next (reply, file))
        (fileEnv env file after frame)) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (NativeM.loopFuel (fun (file, accumulated) => recover_log_loop.body maxRecords file accumulated)
        fuel (file, accumulated) >>= next) (fileEnv env file before frame) := by
  induction fuel generalizing before accumulated with
  | zero =>
      simp only [NativeM.loopFuel, Result.error_bind]
      exact Result.NativeInvariant.error _ _ _ ⟨before, rfl, valid, visible, durable⟩
  | succ fuel ih =>
      rw [NativeM.loopFuel]
      simp only [recover_log_loop.body, monadLift_self, bind_assoc]
      by_cases advance : accumulated.len < maxRecords
      · simp only [advance, ↓reduceIte, bind_assoc]
        apply record_next_invariant env file frame head before _ separate valid visible durable
        intro reply middle admitted v d
        cases reply with
        | Err error =>
            simp only [NativeM.ok, Result.ok_bind]
            exact continuation (.Err error) _ admitted v d
        | Ok option =>
            cases option with
            | none =>
                simp only [NativeM.ok, Result.ok_bind]
                exact continuation (.Ok accumulated) _ admitted v d
            | some value =>
                simp only [NativeM.monadLift_eq, bind_assoc]
                apply from_rust_invariant _ _ ⟨middle, rfl, admitted, v, d⟩
                intro updated
                simp only [NativeM.ok, Result.ok_bind]
                exact ih middle updated admitted v d
      · simp only [advance, ↓reduceIte, NativeM.ok, Result.ok_bind]
        exact continuation (.Ok accumulated) _ valid visible durable

/-- Actual cross-crate reads retain the complete acknowledged prefix for all
host read choices, including short reads, errors, malformed choices and blocking. -/
theorem read_once_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (buffer : Slice U8) (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (io_core.read_once file buffer) (fileEnv env file before frame) := by
  have safe := read_next_invariant env file frame head before buffer Result.ok
    separate valid visible durable (fun reply updated after admitted v d =>
      Result.NativeInvariant.ok _ _ _ ⟨after, rfl, admitted, v, d⟩)
  simpa only [Result.bind_ok] using safe


/-- The actual parser preserves the images at every intermediate native read,
without assuming successful reads or well-formed host scripts. -/
theorem record_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (read_record file) (fileEnv env file before frame) := by
  have safe := record_next_invariant env file frame head before Result.ok
    separate valid visible durable (fun reply after admitted v d =>
      Result.NativeInvariant.ok _ _ _ ⟨after, rfl, admitted, v, d⟩)
  simpa only [Result.bind_ok] using safe

/-- Recovery scans preserve arbitrary bounded acknowledged prefixes across all
host seek/read choices. Completion and returned records are separate properties. -/
theorem recover_log_invariant (env : Environment) (file : NativeFile)
    (frame : List (Nat × String × Term)) (head : ByteArray) (before : State) (maxRecords : Usize)
    (separate : Separate file frame) (valid : Admitted before)
    (visible : Prefix head before.visible) (durable : Prefix head before.durable) :
    Result.NativeInvariant (PrefixInvariant env file frame head)
      (recover_log file maxRecords) (fileEnv env file before frame) := by
  simp only [recover_log, monadLift_self]
  apply seek_next_invariant env file frame head before _ separate valid visible durable
  intro reply after admitted v d
  cases reply with
  | Err error => exact Result.NativeInvariant.ok _ _ _ ⟨after, rfl, admitted, v, d⟩
  | Ok offset =>
      simp only [recover_log_loop, NativeM.loop, monadLift_self]
      have safe := loop_next_invariant env file frame head after (alloc.vec.Vec.new U16)
        maxRecords 262145 Result.ok separate admitted v d
        (fun reply after admitted v d => Result.NativeInvariant.ok _ _ _ ⟨after, rfl, admitted, v, d⟩)
      simpa only [Result.bind_ok] using safe

end Record.RecoveryPrefixInvariant
