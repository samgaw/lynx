module
public import Record.RepairReturnProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RecoveryFrame
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.ResizeProperties Record.CrashProperties Record.LogProperties Record.RepairCrashProperties
  Record.IntegrityProperties

private theorem read_frame (before : State) (buffer : Slice U8)
    (reply : core.result.Result Usize NativeIoError) (after : State) (updated : Slice U8)
    (valid : Valid before) (stable : before.durable = before.visible)
    (step : readStep before buffer = some (reply,after,updated)) :
    after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      before.position ≤ after.position ∧ ∀ count, reply = .Ok count →
        after.position = before.position + count.val ∧ count.val ≤ buffer.val.length := by
  unfold readStep at step
  split at step
  · contradiction
  · cases chosen : action "read" before.script with
    | none => simp [chosen] at step
    | some choice =>
        obtain ⟨success,count,mask,rest⟩ := choice
        simp only [chosen,Option.bind_eq_bind,Option.bind_some] at step
        cases persisted : persist before.durable before.visible mask with
        | none => simp [persisted] at step
        | some data =>
            have same := persist_same before.visible mask data (by simpa only [stable] using persisted)
            subst data
            simp only [persisted,Option.bind_some] at step
            cases success
            · simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at step
              obtain ⟨rfl,rfl,rfl⟩ := step
              exact ⟨rfl,rfl,⟨valid.1,le_rfl,valid.2.2⟩,le_rfl,fun _ equal => by cases equal⟩
            · simp only [↓reduceIte] at step
              split at step
              · rename_i bounded
                split at step
                · rename_i available
                  split at step
                  · contradiction
                  · simp only [Option.some.injEq,Prod.mk.injEq] at step
                    obtain ⟨rfl,rfl,rfl⟩ := step
                    refine ⟨rfl,rfl,⟨valid.1,le_rfl,?_⟩,by dsimp; omega,?_⟩
                    · dsimp
                      have := valid.1
                      have := valid.2.2
                      omega
                    · intro returned equal
                      cases equal
                      simp only [Usize.ofNatCore,UScalar.ofNatCore_val_eq]
                      exact ⟨trivial,bounded⟩
                · contradiction
              · contradiction

private theorem pure_next_returns (computation : RustM α) (next : α → NativeM β)
    (env world : Environment) (returned : β)
    (trace : Result.ReadyPrefix (NativeM.fromRust computation >>= next) env (.ok returned) world) :
    ∃ value, Result.ReadyPrefix (next value) env (.ok returned) world := by
  unfold NativeM.fromRust at trace
  split at trace
  · simp only [Result.ok_bind] at trace
    exact ⟨_,trace⟩
  · simp only [NativeM.fail,Result.error_bind] at trace
    cases trace
  · simp only [Result.error_bind] at trace
    cases trace

/-- Every actual word return retains the stable bytes and file identity.
A complete word consumes exactly two bytes; incomplete words retain the actual
advanced cursor. The bytes following the word are entirely unrestricted. -/
theorem word_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result (Option U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (read_word file) (fileEnv env file before frame) (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      before.position ≤ after.position ∧ ∀ value, reply = .Ok (some value) → after.position = before.position + 2 := by
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind] at trace
  change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
    (fileEnv env file before frame) (.ok (reply,returnedFile)) world at trace
  obtain ⟨first,middle,firstTrace,continuation⟩ := trace.bind_returns
  obtain ⟨first,middleState,buffer,rfl,rfl,_,step⟩ :=
    Record.RepairReturnProperties.read_returns file env frame before (one 0#u8) _ _ separate valid firstTrace
  obtain ⟨v1,d1,valid1,pos1,count1⟩ := read_frame before (one 0#u8) first middleState buffer valid stable step
  cases first with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
      exact ⟨rfl,middleState,rfl,v1,d1,valid1,pos1,fun _ equal => by cases equal⟩
  | Ok count =>
      cases position : count.val with
      | zero =>
          simp only [position,NativeM.ok] at continuation
          cases continuation
          exact ⟨rfl,middleState,rfl,v1,d1,valid1,pos1,fun _ equal => by cases equal⟩
      | succ amount =>
          have one1 := count1 count rfl
          have size : (one 0#u8).val.length = 1 := by simp [one]
          have firstCount : count.val = 1 := by rw [size] at one1; omega
          simp only [position] at continuation
          obtain ⟨second,middle,secondTrace,continuation⟩ := continuation.bind_returns
          obtain ⟨second,after,buffer2,rfl,rfl,_,step2⟩ :=
            Record.RepairReturnProperties.read_returns file env frame middleState (one 0#u8) _ _ separate valid1 secondTrace
          obtain ⟨v2,d2,valid2,pos2,count2⟩ := read_frame middleState (one 0#u8) second after buffer2 valid1 (d1.trans v1.symm) step2
          cases second with
          | Err error =>
              simp only [NativeM.ok] at continuation
              cases continuation
              exact ⟨rfl,after,rfl,v2.trans v1,d2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
          | Ok count =>
              cases position2 : count.val with
              | zero =>
                  simp only [position2,NativeM.ok] at continuation
                  cases continuation
                  exact ⟨rfl,after,rfl,v2.trans v1,d2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
              | succ amount =>
                  have one2 := count2 count rfl
                  have secondCount : count.val = 1 := by rw [size] at one2; omega
                  simp only [position2,NativeM.monadLift_eq] at continuation
                  obtain ⟨low,continuation⟩ := pure_next_returns _ _ _ _ _ continuation
                  obtain ⟨high,continuation⟩ := pure_next_returns _ _ _ _ _ continuation
                  simp only [NativeM.ok] at continuation
                  cases continuation
                  refine ⟨rfl,after,rfl,v2.trans v1,d2.trans v1,valid2,pos1.trans pos2,?_⟩
                  intro value equal
                  rw [one2.1,one1.1,firstCount,secondCount]


/-- The extracted record decoder retains arbitrary stable file contents on every
actual return, including errors and incomplete records. A complete record has
consumed exactly four bytes. -/
theorem record_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result (Option U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (read_record file) (fileEnv env file before frame) (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      before.position ≤ after.position ∧ ∀ value, reply = .Ok (some value) → after.position = before.position + 4 := by
  simp only [read_record,monadLift_self] at trace
  obtain ⟨first,middle,firstTrace,continuation⟩ := trace.bind_returns
  obtain ⟨first,firstFile⟩ := first
  obtain ⟨identity,middleState,rfl,v1,d1,valid1,pos1,count1⟩ :=
    word_returns file env frame before first firstFile middle separate valid stable firstTrace
  subst firstFile
  cases first with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
      exact ⟨rfl,middleState,rfl,v1,d1,valid1,pos1,fun _ equal => by cases equal⟩
  | Ok option =>
      cases option with
      | none =>
          simp only [NativeM.ok] at continuation
          cases continuation
          exact ⟨rfl,middleState,rfl,v1,d1,valid1,pos1,fun _ equal => by cases equal⟩
      | some value =>
          obtain ⟨second,middle,secondTrace,continuation⟩ := continuation.bind_returns
          obtain ⟨second,secondFile⟩ := second
          obtain ⟨identity,after,rfl,v2,d2,valid2,pos2,count2⟩ :=
            word_returns file env frame middleState second secondFile middle separate valid1 (d1.trans v1.symm) secondTrace
          subst secondFile
          cases second with
          | Err error =>
              simp only [NativeM.ok] at continuation
              cases continuation
              exact ⟨rfl,after,rfl,v2.trans v1,d2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
          | Ok option =>
              cases option with
              | none =>
                  simp only [NativeM.ok] at continuation
                  cases continuation
                  exact ⟨rfl,after,rfl,v2.trans v1,d2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
              | some inverse =>
                  simp only [io_core.decode_record,NativeM.lift,monadLift_self,Result.ok_bind] at continuation
                  split at continuation <;> simp only [NativeM.ok,Result.ok_bind] at continuation <;> cases continuation
                  all_goals
                    refine ⟨rfl,after,rfl,v2.trans v1,d2.trans v1,valid2,pos1.trans pos2,?_⟩
                    intro _ _
                    rw [count2 inverse rfl,count1 value rfl]

/-- Each completed actual scan retains every value already accumulated and the
stable byte image, regardless of subsequent bytes or host read choices. Its
returned records fit within the cursor it actually reached. -/
theorem loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (accumulated : alloc.vec.Vec U16) (maxRecords : Usize) (fuel : Nat)
    (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (consumed : 4 * accumulated.val.length ≤ before.position)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
        fuel (file, accumulated)) (fileEnv env file before frame) (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      before.position ≤ after.position ∧ 4 * returned.val.length ≤ after.position ∧
      ∃ suffix, returned.val = accumulated.val ++ suffix := by
  induction fuel generalizing before accumulated with
  | zero => simp only [NativeM.loopFuel] at trace; cases trace
  | succ fuel ih =>
      rw [NativeM.loopFuel] at trace
      conv at trace => arg 1; arg 1; unfold recover_log_loop.body
      simp only [monadLift_self] at trace
      by_cases advance : accumulated.len < maxRecords
      · simp only [advance,↓reduceIte,bind_assoc] at trace
        obtain ⟨record,middle,recordTrace,continuation⟩ := trace.bind_returns
        obtain ⟨record,recordFile⟩ := record
        obtain ⟨identity,middleState,rfl,v,d,valid1,pos,count⟩ :=
          record_returns file env frame before record recordFile middle separate valid stable recordTrace
        subst recordFile
        cases record with
        | Err error =>
            simp only [NativeM.ok,Result.ok_bind] at continuation
            cases continuation
        | Ok option =>
            cases option with
            | none =>
                simp only [NativeM.ok,Result.ok_bind] at continuation
                cases continuation
                exact ⟨rfl,middleState,rfl,v,d,valid1,pos,consumed.trans pos,[],by simp⟩
            | some value =>
                simp only [NativeM.monadLift_eq,Record.Extraction.VectorModel.push_eq] at continuation
                split at continuation
                · simp only [NativeM.fromRust_ok,NativeM.ok,Result.ok_bind] at continuation
                  have nextConsumed : 4 * (accumulated.val ++ [value]).length ≤ middleState.position := by
                    have := count value rfl
                    simp only [List.length_append,List.length_singleton]
                    omega
                  obtain ⟨identity,after,worldEqual,v2,d2,valid2,pos2,bound,suffix,extension⟩ :=
                    ih (before := middleState)
                      (accumulated := alloc.vec.Vec.from (accumulated.val ++ [value]) (by scalar_tac))
                      valid1 (d.trans v.symm) (by simpa only [alloc.vec.Vec.from_val] using nextConsumed) continuation
                  exact ⟨identity,after,worldEqual,v2.trans v,d2.trans v,valid2,pos.trans pos2,
                    bound,value :: suffix,by simpa only [alloc.vec.Vec.from_val,List.append_assoc,List.singleton_append] using extension⟩
                · simp [NativeM.fromRust,RustM.fail] at continuation
                  cases continuation
      · simp only [advance,↓reduceIte,NativeM.ok,Result.ok_bind] at trace
        cases trace
        exact ⟨rfl,before,rfl,rfl,stable,valid,le_rfl,consumed,[],by simp⟩

private theorem known_loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (remaining : List U16) (tail : List U8)
    (accumulated : alloc.vec.Vec U16) (maxRecords : Usize) (fuel : Nat)
    (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = (logBytes remaining ++ tail).map rawByte)
    (consumed : 4 * accumulated.val.length ≤ before.position)
    (countBound : accumulated.val.length ≤ maxRecords.val)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
        fuel (file, accumulated)) (fileEnv env file before frame) (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      (4 * returned.val.length ≤ after.position) ∧
      (returned.val.length = maxRecords.val ∨ ∃ suffix, returned.val = accumulated.val ++ remaining ++ suffix) := by
  induction fuel generalizing remaining before accumulated with
  | zero => simp only [NativeM.loopFuel] at trace; cases trace
  | succ fuel ih =>
      cases remaining with
      | nil =>
          obtain ⟨identity,after,worldEqual,v,d,valid1,_,bound,suffix,extension⟩ :=
            loop_returns file env frame before accumulated maxRecords (fuel + 1) returned returnedFile world
              separate valid stable consumed trace
          exact ⟨identity,after,worldEqual,v,d,valid1,bound,.inr ⟨suffix,by simpa using extension⟩⟩
      | cons value remaining =>
        rw [NativeM.loopFuel] at trace
        conv at trace => arg 1; arg 1; unfold recover_log_loop.body
        simp only [monadLift_self] at trace
        by_cases advance : accumulated.len < maxRecords
        · simp only [advance, ↓reduceIte, bind_assoc] at trace
          obtain ⟨record, midway, recordTrace, continuation⟩ := trace.bind_returns
          obtain ⟨record, recordFile⟩ := record
          cases record with
          | Err error =>
              simp only [NativeM.ok, Result.ok_bind] at continuation
              cases continuation
          | Ok option =>
              have result := Record.RepairReturnProperties.record_returns file env frame before value (logBytes remaining ++ tail)
                option recordFile midway separate valid stable (by
                  simpa only [logBytes, List.flatMap_cons, List.append_assoc] using contents) recordTrace
              obtain ⟨rfl, fileEqual, rest, rfl⟩ := result
              subst recordFile
              have middleValid : Valid (readState before 4 before.visible rest) := by
                refine ⟨valid.1, le_rfl, ?_⟩
                have length := congrArg List.length contents
                simp only [List.length_drop, Array.length_toList, List.length_map, List.length_append,
                  logBytes_length, List.length_cons] at length
                dsimp [readState]
                have := valid.1
                have := before.visible.size_data
                omega
              have remainingContents : before.visible.data.toList.drop (before.position + 4) =
                  (logBytes remaining ++ tail).map rawByte := by
                rw [← List.drop_drop, contents]
                simp [logBytes, layout, Array.make_val, List.map_append]
              have less : accumulated.val.length < maxRecords.val := by
                simpa only [alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore,
                  UScalar.ofNatCore_val_eq] using advance
              simp only [NativeM.monadLift_eq, Record.Extraction.VectorModel.push_eq] at continuation
              split at continuation
              · simp only [NativeM.fromRust_ok, NativeM.ok, Result.ok_bind] at continuation
                have result := ih (remaining := remaining) (before := readState before 4 before.visible rest)
                  (accumulated := alloc.vec.Vec.from (accumulated.val ++ [value]) (by scalar_tac))
                  middleValid rfl remainingContents
                      (by dsimp [readState]; simp only [alloc.vec.Vec.from_val,List.length_append,List.length_singleton]; omega)
                      (by simp; omega) continuation
                obtain ⟨fileEqual, after, worldEqual, v, d, admitted, bound, parsed⟩ := result
                refine ⟨fileEqual, after, worldEqual, v, d, admitted, bound, ?_⟩
                rcases parsed with limit | complete
                · exact .inl limit
                · obtain ⟨suffix,complete⟩ := complete
                  exact .inr ⟨suffix, by simpa only [alloc.vec.Vec.from_val, List.append_assoc, List.singleton_append] using complete⟩
              · simp [NativeM.fromRust, RustM.fail] at continuation
                cases continuation
        · have notLess : ¬ accumulated.val.length < maxRecords.val := by
            simpa only [alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore,
              UScalar.ofNatCore_val_eq] using advance
          have equal : accumulated.val.length = maxRecords.val := by omega
          simp only [advance, ↓reduceIte, NativeM.ok, Result.ok_bind] at trace
          cases trace
          exact ⟨rfl, before, rfl, rfl, stable, valid, consumed, .inl equal⟩


/-- The actual recovery scan is either capped or returns an extension of the
known encoded prefix. The later byte suffix, read script, initial cursor and
persistence masks are arbitrary. This is a successful-return safety theorem;
errors, blocking and exhaustion are not treated as successful recovery. -/
theorem recover_returns_prefix (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (tail : List U8)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible = disk (logBytes values ++ tail))
    (trace : Result.ReadyPrefix (recover_log file maxRecords) (fileEnv env file before frame)
      (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      (4 * returned.val.length ≤ after.position) ∧
      (returned.val.length = maxRecords.val ∨ ∃ suffix, returned.val = values ++ suffix) := by
  simp only [recover_log, monadLift_self] at trace
  obtain ⟨seek, middle, seekTrace, continuation⟩ := trace.bind_returns
  obtain ⟨reply, soughtFile⟩ := seek
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok offset =>
      obtain ⟨fileEqual, rest, rfl⟩ := Record.RepairReturnProperties.seek_returns file env frame before offset soughtFile middle
        separate valid stable seekTrace
      subst soughtFile
      simp only [recover_log_loop, NativeM.loop, monadLift_self] at continuation
      have resetValid : Valid (sought before 0 before.visible rest) :=
        ⟨valid.1, le_rfl, by simp [sought, limit]⟩
      have bytes : (sought before 0 before.visible rest).visible.data.toList.drop
          (sought before 0 before.visible rest).position = (logBytes values ++ tail).map rawByte := by
        simp [sought, contents, disk]
      simpa only [sought, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] using
        known_loop_returns file env frame (sought before 0 before.visible rest) values tail
          (alloc.vec.Vec.new U16) maxRecords _ returned returnedFile world separate resetValid rfl
          bytes (by simp [alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.new]) continuation

end Record.RecoveryFrame
