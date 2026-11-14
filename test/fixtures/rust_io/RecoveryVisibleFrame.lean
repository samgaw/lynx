module
public import Record.RepairReturnProperties
public import Record.RecoveryPrefixInvariant
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RecoveryVisibleFrame
variable [heapLayout : Record.Properties.HeapLayout]
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.ResizeProperties Record.CrashProperties Record.LogProperties Record.RepairCrashProperties
  Record.IntegrityProperties

/-- A completed actual read retains file identity and exposes its actual file-model step. -/
theorem read_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (buffer : Slice U8)
    (output : core.result.Result Usize NativeIoError × NativeFile × Slice U8) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (io_core.read_once file buffer) (fileEnv env file before frame) (.ok output) world) :
    ∃ reply after updated, output = (reply, file, updated) ∧
      world = fileEnv env file after frame ∧ blocked before = false ∧
      readStep before buffer = some (reply, after, updated) := by
  simp only [io_core.read_once, monadLift_self, NativeFile.read] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready rest =>
      cases actual with
      | error exception => cases rest
      | ok output =>
          cases rest
          unfold pollRead at ready
          rw [lookup_admitted env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : readStep before buffer with
            | none => simp [step] at ready
            | some outcome =>
                obtain ⟨reply, after, updated⟩ := outcome
                simp only [step] at ready
                obtain ⟨rfl, rfl⟩ := ready
                exact ⟨reply, after, updated, rfl, store_at env file before after frame separate,
                  by simpa only [Bool.not_eq_true] using stopped, rfl⟩

omit heapLayout in
private theorem read_frame (before : State) (buffer : Slice U8)
    (reply : core.result.Result Usize NativeIoError) (after : State) (updated : Slice U8)
    (valid : Admitted before)
    (step : readStep before buffer = some (reply,after,updated)) :
    after.visible = before.visible ∧ Admitted after ∧
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
            have sizes := persist_lengths _ _ _ _ persisted
            simp only [persisted,Option.bind_some] at step
            cases success
            · simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at step
              obtain ⟨rfl,rfl,rfl⟩ := step
              exact ⟨rfl,⟨valid.1,by dsimp; have := valid.1; have := valid.2.1; omega,valid.2.2⟩,le_rfl,fun _ equal => by cases equal⟩
            · simp only [↓reduceIte] at step
              split at step
              · rename_i bounded
                split at step
                · rename_i available
                  split at step
                  · contradiction
                  · simp only [Option.some.injEq,Prod.mk.injEq] at step
                    obtain ⟨rfl,rfl,rfl⟩ := step
                    refine ⟨rfl,⟨valid.1,by dsimp; have := valid.1; have := valid.2.1; omega,?_⟩,by dsimp; omega,?_⟩
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

omit heapLayout in
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

/-- Every actual word return retains the visible bytes and file identity.
A complete word consumes exactly two bytes; incomplete words retain the actual
advanced cursor. The bytes following the word are entirely unrestricted. -/
theorem word_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result (Option U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (read_word file) (fileEnv env file before frame) (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after ∧
      before.position ≤ after.position ∧ ∀ value, reply = .Ok (some value) → after.position = before.position + 2 := by
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind] at trace
  change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
    (fileEnv env file before frame) (.ok (reply,returnedFile)) world at trace
  obtain ⟨first,middle,firstTrace,continuation⟩ := trace.bind_returns
  obtain ⟨first,middleState,buffer,rfl,rfl,_,step⟩ :=
    read_returns file env frame before (one 0#u8) _ _ separate valid firstTrace
  obtain ⟨v1,valid1,pos1,count1⟩ := read_frame before (one 0#u8) first middleState buffer valid step
  cases first with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
      exact ⟨rfl,middleState,rfl,v1,valid1,pos1,fun _ equal => by cases equal⟩
  | Ok count =>
      cases position : count.val with
      | zero =>
          simp only [position,NativeM.ok] at continuation
          cases continuation
          exact ⟨rfl,middleState,rfl,v1,valid1,pos1,fun _ equal => by cases equal⟩
      | succ amount =>
          have one1 := count1 count rfl
          have size : (one 0#u8).val.length = 1 := by simp [one]
          have firstCount : count.val = 1 := by rw [size] at one1; omega
          simp only [position] at continuation
          obtain ⟨second,middle,secondTrace,continuation⟩ := continuation.bind_returns
          obtain ⟨second,after,buffer2,rfl,rfl,_,step2⟩ :=
            read_returns file env frame middleState (one 0#u8) _ _ separate valid1 secondTrace
          obtain ⟨v2,valid2,pos2,count2⟩ := read_frame middleState (one 0#u8) second after buffer2 valid1 step2
          cases second with
          | Err error =>
              simp only [NativeM.ok] at continuation
              cases continuation
              exact ⟨rfl,after,rfl,v2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
          | Ok count =>
              cases position2 : count.val with
              | zero =>
                  simp only [position2,NativeM.ok] at continuation
                  cases continuation
                  exact ⟨rfl,after,rfl,v2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
              | succ amount =>
                  have one2 := count2 count rfl
                  have secondCount : count.val = 1 := by rw [size] at one2; omega
                  simp only [position2,NativeM.monadLift_eq] at continuation
                  obtain ⟨low,continuation⟩ := pure_next_returns _ _ _ _ _ continuation
                  obtain ⟨high,continuation⟩ := pure_next_returns _ _ _ _ _ continuation
                  simp only [NativeM.ok] at continuation
                  cases continuation
                  refine ⟨rfl,after,rfl,v2.trans v1,valid2,pos1.trans pos2,?_⟩
                  intro value equal
                  rw [one2.1,one1.1,firstCount,secondCount]


/-- The extracted record decoder retains arbitrary file contents on every
actual return, including errors and incomplete records. A complete record has
consumed exactly four bytes. -/
theorem record_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result (Option U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (read_record file) (fileEnv env file before frame) (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after ∧
      before.position ≤ after.position ∧ ∀ value, reply = .Ok (some value) → after.position = before.position + 4 := by
  simp only [read_record,monadLift_self] at trace
  obtain ⟨first,middle,firstTrace,continuation⟩ := trace.bind_returns
  obtain ⟨first,firstFile⟩ := first
  obtain ⟨identity,middleState,rfl,v1,valid1,pos1,count1⟩ :=
    word_returns file env frame before first firstFile middle separate valid firstTrace
  subst firstFile
  cases first with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
      exact ⟨rfl,middleState,rfl,v1,valid1,pos1,fun _ equal => by cases equal⟩
  | Ok option =>
      cases option with
      | none =>
          simp only [NativeM.ok] at continuation
          cases continuation
          exact ⟨rfl,middleState,rfl,v1,valid1,pos1,fun _ equal => by cases equal⟩
      | some value =>
          obtain ⟨second,middle,secondTrace,continuation⟩ := continuation.bind_returns
          obtain ⟨second,secondFile⟩ := second
          obtain ⟨identity,after,rfl,v2,valid2,pos2,count2⟩ :=
            word_returns file env frame middleState second secondFile middle separate valid1 secondTrace
          subst secondFile
          cases second with
          | Err error =>
              simp only [NativeM.ok] at continuation
              cases continuation
              exact ⟨rfl,after,rfl,v2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
          | Ok option =>
              cases option with
              | none =>
                  simp only [NativeM.ok] at continuation
                  cases continuation
                  exact ⟨rfl,after,rfl,v2.trans v1,valid2,pos1.trans pos2,fun _ equal => by cases equal⟩
              | some inverse =>
                  simp only [io_core.decode_record,NativeM.lift,monadLift_self,Result.ok_bind] at continuation
                  split at continuation <;> simp only [NativeM.ok,Result.ok_bind] at continuation <;> cases continuation
                  all_goals
                    refine ⟨rfl,after,rfl,v2.trans v1,valid2,pos1.trans pos2,?_⟩
                    intro _ _
                    rw [count2 inverse rfl,count1 value rfl]

/-- Each completed actual scan retains every value already accumulated and the
visible byte image, regardless of subsequent bytes or host read choices. Its
returned records fit within the cursor it actually reached. -/
theorem loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (accumulated : alloc.vec.Vec U16) (maxRecords : Usize) (fuel : Nat)
    (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (consumed : 4 * accumulated.val.length ≤ before.position)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
        fuel (file, accumulated)) (fileEnv env file before frame) (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after ∧
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
        obtain ⟨identity,middleState,rfl,v,valid1,pos,count⟩ :=
          record_returns file env frame before record recordFile middle separate valid recordTrace
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
                exact ⟨rfl,middleState,rfl,v,valid1,pos,consumed.trans pos,[],by simp⟩
            | some value =>
                simp only [NativeM.monadLift_eq,Record.Extraction.VectorModel.push_eq] at continuation
                split at continuation
                · simp only [NativeM.fromRust_ok,NativeM.ok,Result.ok_bind] at continuation
                  have nextConsumed : 4 * (accumulated.val ++ [value]).length ≤ middleState.position := by
                    have := count value rfl
                    simp only [List.length_append,List.length_singleton]
                    omega
                  obtain ⟨identity,after,worldEqual,v2,valid2,pos2,bound,suffix,extension⟩ :=
                    ih (before := middleState)
                      (accumulated := alloc.vec.Vec.from (accumulated.val ++ [value]) (by scalar_tac))
                      valid1 (by simpa only [alloc.vec.Vec.from_val] using nextConsumed) continuation
                  exact ⟨identity,after,worldEqual,v2.trans v,valid2,pos.trans pos2,
                    bound,value :: suffix,by simpa only [alloc.vec.Vec.from_val,List.append_assoc,List.singleton_append] using extension⟩
                · simp [NativeM.fromRust,RustM.fail] at continuation
                  cases continuation
      · simp only [advance,↓reduceIte,NativeM.ok,Result.ok_bind] at trace
        cases trace
        exact ⟨rfl,before,rfl,rfl,valid,le_rfl,consumed,[],by simp⟩

omit heapLayout in
private theorem read_choice (before : State) (count : Usize) (after : State) (updated : Slice U8)
    (step : readStep before (one 0#u8) = some (.Ok count, after, updated)) :
    ∃ value mask rest, action "read" before.script = some (true, value, mask, rest) ∧
      persist before.durable before.visible mask = some after.durable ∧
      count.val = value ∧ value ≤ 1 ∧ value ≤ before.visible.size - before.position ∧
      ¬(value = 0 ∧ before.position < before.visible.size) := by
  unfold readStep at step
  simp only [one, Slice.from_val, List.length_singleton] at step
  split at step
  · contradiction
  · cases chosen : action "read" before.script with
    | none => simp [chosen] at step
    | some choice =>
        obtain ⟨success, value, mask, rest⟩ := choice
        simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
        cases accepted : persist before.durable before.visible mask with
        | none => simp [accepted] at step
        | some data =>
            simp only [accepted, Option.bind_some] at step
            cases success
            · simp at step
            · simp only [↓reduceIte] at step
              split at step
              · rename_i size
                split at step
                · rename_i available
                  split at step
                  · contradiction
                  · rename_i progress
                    simp only [Option.some.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at step
                    obtain ⟨rfl, rfl, rfl⟩ := step
                    exact ⟨value, mask, rest, rfl, accepted,
                      by simp [Usize.ofNatCore], size, available, by omega⟩
                · contradiction
              · contradiction

omit heapLayout in
private theorem read_byte (before : State) (byte : UInt8) (tail : List UInt8)
    (count : Usize) (after : State) (updated : Slice U8)
    (contents : before.visible.data.toList.drop before.position = byte :: tail)
    (step : readStep before (one 0#u8) = some (.Ok count, after, updated)) :
    ∃ durable rest, count = 1#usize ∧ after = readState before 1 durable rest ∧
      updated = one (byteValue byte) := by
  obtain ⟨value, mask, rest, chosen, accepted, returned, size, available, progress⟩ := read_choice before count after updated step
  have length := congrArg List.length contents
  simp only [List.length_drop, Array.length_toList, List.length_cons] at length
  have countOne : value = 1 := by have := before.visible.size_data; omega
  rw [countOne] at chosen
  have expected := read_one_step before byte tail mask after.durable rest contents chosen accepted
  rw [expected] at step
  simp only [Option.some.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at step
  obtain ⟨countEqual,afterEqual,bufferEqual⟩ := step
  exact ⟨after.durable,rest,countEqual.symm,afterEqual.symm,bufferEqual.symm⟩


private theorem read_next (file : NativeFile) (buffer : Slice U8) (env : Environment)
    (frame : List (Nat × String × Term)) (before after : State)
    (reply : core.result.Result Usize NativeIoError) (updated : Slice U8)
    (separate : Separate file frame) (valid : Admitted before)
    (notBlocked : blocked before = false)
    (step : readStep before buffer = some (reply, after, updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (io_core.read_once file buffer >>= next).run (fileEnv env file before frame) =
      (next (reply, file, updated)).run (fileEnv env file after frame) := by
  have ready : pollRead file buffer (fileEnv env file before frame) =
      some (.ok (reply, file, updated), fileEnv env file after frame) := by
    simp [pollRead, lookup_admitted env file before frame separate valid, notBlocked,
      step, store_at env file before after frame separate]
  simp only [io_core.read_once, monadLift_self, NativeFile.read, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp [Result.ok_bind]

/-- Unfold the real parser, including both mutable array reconstructions,
checked element projections and little-endian decoding. -/
private theorem parser_ready (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before middle after : State) (low high : U8)
    (separate : Separate file frame) (valid : Admitted before) (validMiddle : Admitted middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one low))
    (second : readStep middle (one 0#u8) = some (.Ok 1#usize, after, one high)) :
    (read_word file).run (fileEnv env file before frame) =
      (.ok (.Ok (some (word low high)), file), fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _).run _ = _
  rw [read_next file (one 0#u8) env frame before middle _ (one low)
    separate valid notBlocked first]
  change (io_core.read_once file (one 0#u8) >>= _).run _ = _
  rw [read_next file (one 0#u8) env frame middle after _ (one high)
    separate validMiddle notBlockedMiddle second]
  simp [NativeM.ok, Array.from_slice,
    one, Array.index_usize, NativeM.monadLift_eq, NativeM.fromRust,
    word, Result.ok_bind, Result.ok_apply]


/-- A complete visible word is decoded correctly for arbitrary durable bytes.
The returned cursor and heap remain those of the actual two reads. -/
private theorem known_word_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (low high : UInt8) (tail : List UInt8)
    (option : Option U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (contents : before.visible.data.toList.drop before.position = low :: high :: tail)
    (trace : Result.ReadyPrefix (read_word file) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError),returnedFile)) world) :
    option = some (word (byteValue low) (byteValue high)) ∧ returnedFile = file ∧ ∃ after,
      world = fileEnv env file after frame ∧ after.visible = before.visible ∧ Admitted after ∧
      after.position = before.position + 2 := by
  have generic := word_returns file env frame before (.Ok option) returnedFile world separate valid trace
  have originalTrace := trace
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind] at trace
  change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
    (fileEnv env file before frame) (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError),returnedFile)) world at trace
  obtain ⟨first,midway,firstTrace,continuation⟩ := trace.bind_returns
  obtain ⟨first,middle,buffer,rfl,rfl,ready0,step0⟩ := read_returns file env frame before (one 0#u8) _ _ separate valid firstTrace
  have middleValid := (read_frame before _ first middle buffer valid step0).2.1
  cases first with
  | Err error => simp only [NativeM.ok] at continuation; cases continuation
  | Ok count =>
      obtain ⟨durable1,rest1,rfl,rfl,rfl⟩ := read_byte before low (high :: tail) count middle buffer contents step0
      have remaining : before.visible.data.toList.drop (before.position + 1) = high :: tail := by
        rw [← List.drop_drop,contents]; rfl
      change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
        (fileEnv env file (readState before 1 durable1 rest1) frame)
        (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError),returnedFile)) world at continuation
      obtain ⟨second,midway,secondTrace,continuation⟩ := continuation.bind_returns
      obtain ⟨second,after,buffer,rfl,rfl,ready1,step1⟩ := read_returns file env frame _ (one 0#u8) _ _ separate middleValid secondTrace
      cases second with
      | Err error => simp only [NativeM.ok] at continuation; cases continuation
      | Ok count =>
          obtain ⟨durable2,rest2,rfl,rfl,rfl⟩ := read_byte _ high tail count after buffer remaining step1
          have expected := parser_ready file env frame before (readState before 1 durable1 rest1)
            (readState (readState before 1 durable1 rest1) 1 durable2 rest2)
            (byteValue low) (byteValue high) separate valid middleValid ready0 ready1 step0 step1
          have observed := originalTrace.run []
          rw [Result.ok_apply] at observed
          have equal := expected.symm.trans observed
          simp only [Prod.mk.injEq,Outcome.ok.injEq,core.result.Result.Ok.injEq] at equal
          have decoded := equal.1.1.symm
          refine ⟨decoded,generic.1,?_⟩
          obtain ⟨final,worldEqual,visible,admitted,position,consumed⟩ := generic.2
          exact ⟨final,worldEqual,visible,admitted,consumed _ (by rw [decoded])⟩


/-- The real complement-checked decoder returns the known visible record,
without requiring the durable bytes to equal the visible bytes. -/
theorem known_record_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (value : U16) (tail : List U8)
    (option : Option U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (contents : before.visible.data.toList.drop before.position = ((layout value).val ++ tail).map rawByte)
    (trace : Result.ReadyPrefix (read_record file) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError),returnedFile)) world) :
    option = some value ∧ returnedFile = file ∧ ∃ after,
      world = fileEnv env file after frame ∧ after.visible = before.visible ∧ Admitted after ∧
      after.position = before.position + 4 := by
  have generic := record_returns file env frame before (.Ok option) returnedFile world separate valid trace
  have bytes0 : before.visible.data.toList.drop before.position =
      rawByte (low value) :: rawByte (high value) :: rawByte (low (~~~value)) ::
        rawByte (high (~~~value)) :: tail.map rawByte := by
    simpa only [layout,Array.make_val,List.cons_append,List.nil_append,List.map_cons] using contents
  simp only [read_record,monadLift_self] at trace
  obtain ⟨⟨first,firstFile⟩,midway,firstTrace,continuation⟩ := trace.bind_returns
  cases first with
  | Err error => simp only [NativeM.ok] at continuation; cases continuation
  | Ok first =>
      have result := known_word_returns file env frame before _ _ _ first firstFile midway separate valid bytes0 firstTrace
      simp only [byte_roundtrip] at result
      obtain ⟨rfl,fileEqual,middle,rfl,v,admitted,position⟩ := result
      subst firstFile
      have remaining : middle.visible.data.toList.drop middle.position =
          rawByte (low (~~~value)) :: rawByte (high (~~~value)) :: tail.map rawByte := by
        rw [v,position,← List.drop_drop,bytes0]; rfl
      obtain ⟨⟨second,secondFile⟩,midway,secondTrace,continuation⟩ := continuation.bind_returns
      cases second with
      | Err error => simp only [NativeM.ok] at continuation; cases continuation
      | Ok second =>
          have result := known_word_returns file env frame middle _ _ _ second secondFile midway separate admitted remaining secondTrace
          simp only [byte_roundtrip] at result
          obtain ⟨rfl,fileEqual,after,rfl,v2,admitted2,position2⟩ := result
          subst secondFile
          simp only [decode_layout,NativeM.ok,Result.ok_bind] at continuation
          cases continuation
          refine ⟨rfl,rfl,?_⟩
          obtain ⟨final,worldEqual,visible,valid,monotone,consumed⟩ := generic.2
          exact ⟨final,worldEqual,visible,valid,consumed _ rfl⟩

private theorem known_loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (remaining : List U16) (tail : List U8)
    (accumulated : alloc.vec.Vec U16) (maxRecords : Usize) (fuel : Nat)
    (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (contents : before.visible.data.toList.drop before.position = (logBytes remaining ++ tail).map rawByte)
    (consumed : 4 * accumulated.val.length ≤ before.position)
    (countBound : accumulated.val.length ≤ maxRecords.val)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
        fuel (file, accumulated)) (fileEnv env file before frame) (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after ∧
      (4 * returned.val.length ≤ after.position) ∧
      (returned.val.length = maxRecords.val ∨ ∃ suffix, returned.val = accumulated.val ++ remaining ++ suffix) := by
  induction fuel generalizing remaining before accumulated with
  | zero => simp only [NativeM.loopFuel] at trace; cases trace
  | succ fuel ih =>
      cases remaining with
      | nil =>
          obtain ⟨identity,after,worldEqual,v,valid1,_,bound,suffix,extension⟩ :=
            loop_returns file env frame before accumulated maxRecords (fuel + 1) returned returnedFile world
              separate valid consumed trace
          exact ⟨identity,after,worldEqual,v,valid1,bound,.inr ⟨suffix,by simpa using extension⟩⟩
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
              have result := known_record_returns file env frame before value (logBytes remaining ++ tail)
                option recordFile midway separate valid (by
                  simpa only [logBytes, List.flatMap_cons, List.append_assoc] using contents) recordTrace
              obtain ⟨rfl,fileEqual,middle,rfl,visible,middleValid,position⟩ := result
              subst recordFile
              have remainingContents : middle.visible.data.toList.drop middle.position =
                  (logBytes remaining ++ tail).map rawByte := by
                rw [visible,position,← List.drop_drop,contents]
                simp [logBytes,layout,Array.make_val,List.map_append]
              have less : accumulated.val.length < maxRecords.val := by
                simpa only [alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore,
                  UScalar.ofNatCore_val_eq] using advance
              simp only [NativeM.monadLift_eq, Record.Extraction.VectorModel.push_eq] at continuation
              split at continuation
              · simp only [NativeM.fromRust_ok, NativeM.ok, Result.ok_bind] at continuation
                have result := ih (remaining := remaining) (before := middle)
                  (accumulated := alloc.vec.Vec.from (accumulated.val ++ [value]) (by scalar_tac))
                  middleValid remainingContents
                      (by simp only [alloc.vec.Vec.from_val,List.length_append,List.length_singleton]; omega)
                      (by simp; omega) continuation
                obtain ⟨fileEqual, after, worldEqual, v, admitted, bound, parsed⟩ := result
                refine ⟨fileEqual, after, worldEqual, v.trans visible, admitted, bound, ?_⟩
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
          exact ⟨rfl, before, rfl, rfl, valid, consumed, .inl equal⟩

omit heapLayout in
private theorem seek_frame (before : State) (reply : core.result.Result U64 NativeIoError) (after : State)
    (valid : Admitted before)
    (step : seekStep before (.start 0#u64) = some (reply,after)) :
    after.visible = before.visible ∧ Admitted after ∧ ∀ offset, reply = .Ok offset → after.position = 0 := by
  unfold seekStep at step
  cases chosen : action "seek" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success,count,mask,rest⟩ := choice
      simp only [chosen,Option.bind_eq_bind,Option.bind_some] at step
      cases persisted : persist before.durable before.visible mask with
      | none => simp [persisted] at step
      | some data =>
          have sizes := persist_lengths _ _ _ _ persisted
          simp only [persisted,Option.bind_some] at step
          cases success
          · simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq,Prod.mk.injEq] at step
            obtain ⟨rfl,rfl⟩ := step
            exact ⟨rfl,⟨valid.1,by dsimp; have := valid.1; have := valid.2.1; omega,valid.2.2⟩,fun _ equal => by cases equal⟩
          · simp only [↓reduceIte] at step
            split at step
            · contradiction
            · simp only [Option.some.injEq,Prod.mk.injEq] at step
              obtain ⟨rfl,rfl⟩ := step
              exact ⟨rfl,⟨valid.1,by dsimp; have := valid.1; have := valid.2.1; omega,by simp [seekTarget,limit]⟩,fun _ _ => by simp [seekTarget]⟩

private theorem seek_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (reply : core.result.Result U64 NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (io_core.seek_to file 0#u64) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after ∧ ∀ offset, reply = .Ok offset → after.position = 0 := by
  simp only [io_core.seek_to,io_core.seek_from,Record.Extraction.FileModel.seek,NativeFile.seek,monadLift_self] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollSeek at ready
          rw [lookup_admitted env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : seekStep before (.start 0#u64) with
            | none => simp [step] at ready
            | some outcome =>
                obtain ⟨reply,after⟩ := outcome
                simp only [step] at ready
                obtain ⟨rfl,rfl⟩ := ready
                exact ⟨rfl,after,store_at env file before after frame separate,seek_frame before _ after valid step⟩


/-- Recovery scans return a capped prefix or an extension of known records
from the actual visible bytes, with no equality or size ordering assumed between
the initial visible and durable images. -/
theorem recover_returns_prefix (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (tail : List U8)
    (maximum : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (contents : before.visible = disk (logBytes values ++ tail))
    (trace : Result.ReadyPrefix (recover_log file maximum) (fileEnv env file before frame)
      (.ok (.Ok returned,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after ∧ 4 * returned.val.length ≤ after.position ∧
      (returned.val.length = maximum.val ∨ ∃ suffix, returned.val = values ++ suffix) := by
  simp only [recover_log,monadLift_self] at trace
  obtain ⟨⟨reply,soughtFile⟩,middle,seekTrace,continuation⟩ := trace.bind_returns
  cases reply with
  | Err error => simp only [NativeM.ok] at continuation; cases continuation
  | Ok offset =>
      obtain ⟨identity,sought,rfl,visible,admitted,position⟩ := seek_returns file env frame before (.Ok offset) soughtFile middle separate valid seekTrace
      subst soughtFile
      simp only [recover_log_loop,NativeM.loop,monadLift_self] at continuation
      have bytes : sought.visible.data.toList.drop sought.position = (logBytes values ++ tail).map rawByte := by
        rw [position offset rfl,visible,contents]
        simp [disk]
      obtain ⟨identity,after,worldEqual,v,valid1,bound,parsed⟩ := known_loop_returns file env frame sought values tail
        (alloc.vec.Vec.new U16) maximum _ returned returnedFile world separate admitted bytes
        (by simp [alloc.vec.Vec.new]) (by simp [alloc.vec.Vec.new]) continuation
      exact ⟨identity,after,worldEqual,v.trans visible,valid1,bound,
        by simpa only [alloc.vec.Vec.new,alloc.vec.Vec.from_val,List.nil_append] using parsed⟩

private theorem result_loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (accumulated : alloc.vec.Vec U16) (maximum : Usize) (fuel : Nat)
    (reply : core.result.Result (alloc.vec.Vec U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file,values) => recover_log_loop.body maximum file values) fuel (file,accumulated))
      (fileEnv env file before frame) (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after := by
  induction fuel generalizing before accumulated with
  | zero => simp only [NativeM.loopFuel] at trace; cases trace
  | succ fuel ih =>
      rw [NativeM.loopFuel] at trace
      conv at trace => arg 1; arg 1; unfold recover_log_loop.body
      simp only [monadLift_self] at trace
      by_cases advance : accumulated.len < maximum
      · simp only [advance,↓reduceIte,bind_assoc] at trace
        obtain ⟨⟨record,recordFile⟩,middle,recordTrace,continuation⟩ := trace.bind_returns
        obtain ⟨identity,after,rfl,v,valid1,_,_⟩ :=
          record_returns file env frame before record recordFile middle separate valid recordTrace
        subst recordFile
        cases record with
        | Err error =>
            simp only [NativeM.ok,Result.ok_bind] at continuation
            cases continuation
            exact ⟨rfl,after,rfl,v,valid1⟩
        | Ok option =>
            cases option with
            | none =>
                simp only [NativeM.ok,Result.ok_bind] at continuation
                cases continuation
                exact ⟨rfl,after,rfl,v,valid1⟩
            | some value =>
                simp only [NativeM.monadLift_eq,Record.Extraction.VectorModel.push_eq] at continuation
                split at continuation
                · simp only [NativeM.fromRust_ok,NativeM.ok,Result.ok_bind] at continuation
                  obtain ⟨identity,final,worldEqual,v2,valid2⟩ := ih (before := after)
                    (accumulated := alloc.vec.Vec.from (accumulated.val ++ [value]) (by scalar_tac))
                    valid1 continuation
                  exact ⟨identity,final,worldEqual,v2.trans v,valid2⟩
                · simp [NativeM.fromRust,RustM.fail] at continuation
                  cases continuation
      · simp only [advance,↓reduceIte,NativeM.ok,Result.ok_bind] at trace
        cases trace
        exact ⟨rfl,before,rfl,rfl,valid⟩

/-- Every actual recovery return, including I/O errors, retains the borrowed
file identity and visible bytes. Blocking, panic and exhaustion do not fabricate
a returned file. Later bytes and host scripts are arbitrary. -/
theorem recover_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (maximum : Usize)
    (reply : core.result.Result (alloc.vec.Vec U16) NativeIoError) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Admitted before)
    (trace : Result.ReadyPrefix (recover_log file maximum) (fileEnv env file before frame)
      (.ok (reply,returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ Admitted after := by
  simp only [recover_log,monadLift_self] at trace
  obtain ⟨⟨sought,soughtFile⟩,middle,seekTrace,continuation⟩ := trace.bind_returns
  obtain ⟨identity,after,rfl,v,valid1,_⟩ := seek_returns file env frame before sought soughtFile middle separate valid seekTrace
  subst soughtFile
  cases sought with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
      exact ⟨rfl,after,rfl,v,valid1⟩
  | Ok offset =>
      simp only [recover_log_loop,NativeM.loop,monadLift_self] at continuation
      obtain ⟨identity,final,worldEqual,v2,valid2⟩ := result_loop_returns file env frame after
        (alloc.vec.Vec.new U16) maximum _ reply returnedFile world separate valid1 continuation
      exact ⟨identity,final,worldEqual,v2.trans v,valid2⟩

end Record.RecoveryVisibleFrame
