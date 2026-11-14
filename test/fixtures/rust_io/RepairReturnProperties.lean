module
public import Record.RecoveryScanInvariant
public import Record.RepeatedRepairProperties
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairReturnProperties
variable [heapLayout : Record.Properties.HeapLayout]
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.LogProperties Record.TailProperties Record.ResizeProperties Record.RepairCrashProperties

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

private theorem read_byte (before : State) (byte : UInt8) (tail : List UInt8)
    (count : Usize) (after : State) (updated : Slice U8)
    (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = byte :: tail)
    (step : readStep before (one 0#u8) = some (.Ok count, after, updated)) :
    ∃ rest, count = 1#usize ∧ after = readState before 1 before.visible rest ∧
      updated = one (byteValue byte) := by
  obtain ⟨value, mask, rest, chosen, accepted, returned, size, available, progress⟩ := read_choice before count after updated step
  have length := congrArg List.length contents
  simp only [List.length_drop, Array.length_toList, List.length_cons] at length
  have countOne : value = 1 := by have := before.visible.size_data; omega
  rw [countOne] at chosen
  have same := persist_same before.visible mask after.durable (by simpa only [stable] using accepted)
  have expected := read_one_step before byte tail mask before.visible rest contents chosen (by simpa only [same] using accepted)
  rw [expected] at step
  simp only [Option.some.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at step
  obtain ⟨rfl, rfl, rfl⟩ := step
  exact ⟨rest, rfl, rfl, rfl⟩


private theorem read_eof_return (before : State) (count : Usize) (after : State) (updated : Slice U8)
    (stable : before.durable = before.visible) (eof : before.visible.size ≤ before.position)
    (step : readStep before (one 0#u8) = some (.Ok count, after, updated)) :
    ∃ rest, count = 0#usize ∧ after = readState before 0 before.visible rest ∧ updated = one 0#u8 := by
  obtain ⟨value, mask, rest, chosen, accepted, returned, size, available, progress⟩ := read_choice before count after updated step
  have zero : value = 0 := by omega
  rw [zero] at chosen
  have same := persist_same before.visible mask after.durable (by simpa only [stable] using accepted)
  have expected := eof_step before mask before.visible rest eof chosen (by simpa only [same] using accepted)
  rw [expected] at step
  simp only [Option.some.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at step
  obtain ⟨rfl, rfl, rfl⟩ := step
  exact ⟨rest, rfl, rfl, rfl⟩

/-- A completed actual read retains file identity and exposes its actual file-model step. -/
theorem read_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (buffer : Slice U8)
    (output : core.result.Result Usize NativeIoError × NativeFile × Slice U8) (world : Environment)
    (separate : Separate file frame) (valid : Valid before)
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
          rw [lookup_at env file before frame separate valid] at ready
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


private theorem word_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (low high : UInt8) (tail : List UInt8)
    (option : Option U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = low :: high :: tail)
    (trace : Result.ReadyPrefix (read_word file) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world) :
    option = some (word (byteValue low) (byteValue high)) ∧ returnedFile = file ∧
      ∃ rest, world = fileEnv env file (readState before 2 before.visible rest) frame := by
  have originalTrace := trace
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind] at trace
  change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
    (fileEnv env file before frame) (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world at trace
  obtain ⟨first, midway, firstTrace, continuation⟩ := trace.bind_returns
  obtain ⟨first, middle, buffer, rfl, rfl, ready0, step0⟩ :=
    read_returns file env frame before (one 0#u8) _ _ separate valid firstTrace
  cases first with
  | Err error =>
      simp only [NativeM.ok, monadLift_self] at continuation
      cases continuation
  | Ok count =>
      obtain ⟨rest1, rfl, rfl, rfl⟩ := read_byte before low (high :: tail) count middle buffer stable contents step0
      have middleValid : Valid (readState before 1 before.visible rest1) := by
        refine ⟨valid.1, le_rfl, ?_⟩
        have length := congrArg List.length contents
        simp only [List.length_drop, Array.length_toList, List.length_cons, ByteArray.size_data] at length
        dsimp [readState]
        have := valid.1
        have := before.visible.size_data
        omega
      have remaining : before.visible.data.toList.drop (before.position + 1) = high :: tail := by
        rw [← List.drop_drop, contents]
        rfl
      change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
        (fileEnv env file (readState before 1 before.visible rest1) frame)
        (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world at continuation
      obtain ⟨second, midway, secondTrace, continuation⟩ := continuation.bind_returns
      obtain ⟨second, after, buffer, rfl, rfl, ready1, step1⟩ :=
        read_returns file env frame _ (one 0#u8) _ _ separate middleValid secondTrace
      cases second with
      | Err error =>
          simp only [NativeM.ok, monadLift_self] at continuation
          cases continuation
      | Ok count =>
          obtain ⟨rest2, rfl, rfl, rfl⟩ := read_byte _ high tail count after buffer rfl remaining step1
          have expected := parser_ready file env frame before
            (readState before 1 before.visible rest1)
            (readState (readState before 1 before.visible rest1) 1 before.visible rest2)
            (byteValue low) (byteValue high) separate valid middleValid ready0 ready1 step0 step1
          have observed := originalTrace.run []
          rw [Result.ok_apply] at observed
          have equality := expected.symm.trans observed
          simp only [Prod.mk.injEq, Outcome.ok.injEq, core.result.Result.Ok.injEq] at equality
          refine ⟨equality.1.1.symm, equality.1.2.symm, rest2, ?_⟩
          simpa only [readState, Nat.add_assoc] using equality.2.symm


private theorem word_short_return (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (tail : List UInt8)
    (option : Option U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = tail) (short : tail.length < 2)
    (trace : Result.ReadyPrefix (read_word file) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world) :
    option = none ∧ returnedFile = file ∧
      ∃ rest, world = fileEnv env file (readState before tail.length before.visible rest) frame := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind] at trace
  change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
    (fileEnv env file before frame)
    (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world at trace
  obtain ⟨first, midway, firstTrace, continuation⟩ := trace.bind_returns
  obtain ⟨first, middle, buffer, rfl, rfl, ready0, step0⟩ :=
    read_returns file env frame before (one 0#u8) _ _ separate valid firstTrace
  cases first with
  | Err error =>
      simp only [NativeM.ok, monadLift_self] at continuation
      cases continuation
  | Ok count =>
      cases tail with
      | nil =>
          have eof : before.visible.size ≤ before.position := by
            have length := congrArg List.length contents
            simp only [List.length_drop, Array.length_toList, ByteArray.size_data, List.length_nil] at length
            omega
          obtain ⟨rest, rfl, rfl, rfl⟩ := read_eof_return before count middle buffer stable eof step0
          simp only [NativeM.ok, monadLift_self] at continuation
          cases continuation
          exact ⟨rfl, rfl, rest, rfl⟩
      | cons byte tail =>
          have empty : tail = [] := by
            cases tail with
            | nil => rfl
            | cons byte tail => simp only [List.length_cons] at short; omega
          subst tail
          obtain ⟨rest1, rfl, rfl, rfl⟩ := read_byte before byte [] count middle buffer stable contents step0
          have eof : before.visible.size = before.position + 1 := by
            have length := congrArg List.length contents
            simp only [List.length_drop, Array.length_toList, ByteArray.size_data, List.length_cons, List.length_nil] at length
            omega
          have middleValid : Valid (readState before 1 before.visible rest1) :=
            ⟨valid.1, le_rfl, by dsimp [readState]; have := valid.1; omega⟩
          change Result.ReadyPrefix (io_core.read_once file (one 0#u8) >>= _)
            (fileEnv env file (readState before 1 before.visible rest1) frame)
            (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world at continuation
          obtain ⟨second, midway, secondTrace, continuation⟩ := continuation.bind_returns
          obtain ⟨second, after, buffer, rfl, rfl, ready1, step1⟩ :=
            read_returns file env frame _ (one 0#u8) _ _ separate middleValid secondTrace
          cases second with
          | Err error =>
              simp only [NativeM.ok, monadLift_self] at continuation
              cases continuation
          | Ok count =>
              obtain ⟨rest2, rfl, rfl, rfl⟩ := read_eof_return _ count after buffer rfl (by dsimp [readState]; omega) step1
              simp only [NativeM.ok, monadLift_self] at continuation
              cases continuation
              exact ⟨rfl, rfl, rest2, rfl⟩


/-- A known encoded record is decoded before any arbitrary following bytes. -/
theorem record_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (value : U16) (tail : List U8)
    (option : Option U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = ((layout value).val ++ tail).map rawByte)
    (trace : Result.ReadyPrefix (read_record file) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world) :
    option = some value ∧ returnedFile = file ∧
      ∃ rest, world = fileEnv env file (readState before 4 before.visible rest) frame := by
  have bytes0 : before.visible.data.toList.drop before.position =
      rawByte (low value) :: rawByte (high value) :: rawByte (low (~~~value)) ::
        rawByte (high (~~~value)) :: tail.map rawByte := by
    simpa only [layout, Array.make_val, List.cons_append, List.nil_append, List.map_cons] using contents
  simp only [read_record, monadLift_self] at trace
  obtain ⟨first, midway, firstTrace, continuation⟩ := trace.bind_returns
  obtain ⟨first, firstFile⟩ := first
  cases first with
  | Err error =>
      simp only [NativeM.ok, monadLift_self] at continuation
      cases continuation
  | Ok first =>
      have result := word_returns file env frame before _ _ _ first firstFile midway separate valid stable bytes0 firstTrace
      simp only [byte_roundtrip] at result
      obtain ⟨rfl, fileEqual, rest1, rfl⟩ := result
      subst firstFile
      have middleValid : Valid (readState before 2 before.visible rest1) := by
        refine ⟨valid.1, le_rfl, ?_⟩
        have length := congrArg List.length bytes0
        simp only [List.length_drop, Array.length_toList, List.length_cons] at length
        dsimp [readState]
        have := valid.1
        have := before.visible.size_data
        omega
      have remaining : before.visible.data.toList.drop (before.position + 2) =
          rawByte (low (~~~value)) :: rawByte (high (~~~value)) :: tail.map rawByte := by
        rw [← List.drop_drop, bytes0]
        rfl
      change Result.ReadyPrefix (read_word file >>= _)
        (fileEnv env file (readState before 2 before.visible rest1) frame)
        (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world at continuation
      obtain ⟨second, midway, secondTrace, continuation⟩ := continuation.bind_returns
      obtain ⟨second, secondFile⟩ := second
      cases second with
      | Err error =>
          simp only [NativeM.ok, monadLift_self] at continuation
          cases continuation
      | Ok second =>
          have result := word_returns file env frame _ _ _ _ second secondFile midway separate middleValid rfl remaining secondTrace
          simp only [byte_roundtrip] at result
          obtain ⟨rfl, fileEqual, rest2, rfl⟩ := result
          subst secondFile
          simp only [decode_layout, NativeM.ok, monadLift_self, Result.ok_bind] at continuation
          cases continuation
          exact ⟨rfl, rfl, rest2, by simp [readState, Nat.add_assoc]⟩


private theorem record_short_return (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (tail : List UInt8)
    (option : Option U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = tail) (short : tail.length < 4)
    (trace : Result.ReadyPrefix (read_record file) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world) :
    option = none ∧ returnedFile = file ∧
      ∃ rest, world = fileEnv env file (readState before tail.length before.visible rest) frame := by
  simp only [read_record, monadLift_self] at trace
  obtain ⟨first, midway, firstTrace, continuation⟩ := trace.bind_returns
  obtain ⟨first, firstFile⟩ := first
  cases first with
  | Err error =>
      simp only [NativeM.ok, monadLift_self] at continuation
      cases continuation
  | Ok first =>
      by_cases shortWord : tail.length < 2
      · have result := word_short_return file env frame before tail first firstFile midway
          separate valid stable contents shortWord firstTrace
        obtain ⟨rfl, fileEqual, rest, rfl⟩ := result
        subst firstFile
        simp only [NativeM.ok, monadLift_self] at continuation
        cases continuation
        exact ⟨rfl, rfl, rest, rfl⟩
      · cases tail with
        | nil => simp at shortWord
        | cons low tail =>
            cases tail with
            | nil => simp at shortWord
            | cons high tail =>
                have result := word_returns file env frame before low high tail first firstFile midway
                  separate valid stable contents firstTrace
                obtain ⟨rfl, fileEqual, rest1, rfl⟩ := result
                subst firstFile
                have middleValid : Valid (readState before 2 before.visible rest1) := by
                  refine ⟨valid.1, le_rfl, ?_⟩
                  have length := congrArg List.length contents
                  simp only [List.length_drop, Array.length_toList, List.length_cons] at length
                  dsimp [readState]
                  have := valid.1
                  have := before.visible.size_data
                  omega
                have remaining : before.visible.data.toList.drop (before.position + 2) = tail := by
                  rw [← List.drop_drop, contents]
                  rfl
                change Result.ReadyPrefix (read_word file >>= _)
                  (fileEnv env file (readState before 2 before.visible rest1) frame)
                  (.ok ((core.result.Result.Ok option : core.result.Result (Option U16) NativeIoError), returnedFile)) world at continuation
                obtain ⟨second, midway, secondTrace, continuation⟩ := continuation.bind_returns
                obtain ⟨second, secondFile⟩ := second
                cases second with
                | Err error =>
                    simp only [NativeM.ok, monadLift_self] at continuation
                    cases continuation
                | Ok second =>
                    have result := word_short_return file env frame _ tail second secondFile midway separate middleValid
                      rfl remaining (by simp only [List.length_cons] at short; omega) secondTrace
                    obtain ⟨rfl, fileEqual, rest2, rfl⟩ := result
                    subst secondFile
                    simp only [NativeM.ok, monadLift_self] at continuation
                    cases continuation
                    exact ⟨rfl, rfl, rest2, by simp [readState, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩


private theorem loop_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (remaining : List U16) (tail : List U8)
    (accumulated : alloc.vec.Vec U16) (maxRecords : Usize) (fuel : Nat)
    (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible.data.toList.drop before.position = (logBytes remaining ++ tail).map rawByte)
    (short : tail.length < 4) (countBound : accumulated.val.length ≤ maxRecords.val)
    (trace : Result.ReadyPrefix
      (NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
        fuel (file, accumulated)) (fileEnv env file before frame) (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      (returned.val.length = maxRecords.val ∨ returned.val = accumulated.val ++ remaining) := by
  induction fuel generalizing remaining before accumulated with
  | zero => simp only [NativeM.loopFuel] at trace; cases trace
  | succ fuel ih =>
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
            cases remaining with
            | nil =>
                have result := record_short_return file env frame before (tail.map rawByte) option recordFile midway
                  separate valid stable (by simpa only [logBytes, List.flatMap_nil, List.nil_append] using contents)
                  (by simpa only [List.length_map] using short) recordTrace
                obtain ⟨rfl, fileEqual, rest, rfl⟩ := result
                subst recordFile
                simp only [NativeM.ok, Result.ok_bind] at continuation
                cases continuation
                refine ⟨rfl, readState before (tail.map rawByte).length before.visible rest, rfl, rfl, rfl, ?_, .inr (by simp)⟩
                refine ⟨valid.1, le_rfl, ?_⟩
                have length := congrArg List.length contents
                simp only [logBytes, List.flatMap_nil, List.nil_append, List.length_map,
                  List.length_drop, Array.length_toList, ByteArray.size_data] at length
                dsimp [readState]
                simp only [List.length_map]
                have := valid.1
                have := valid.2.2
                omega
            | cons value remaining =>
                have result := record_returns file env frame before value (logBytes remaining ++ tail)
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
                    middleValid rfl remainingContents (by simp; omega) continuation
                  obtain ⟨fileEqual, after, worldEqual, v, d, admitted, parsed⟩ := result
                  refine ⟨fileEqual, after, worldEqual, v, d, admitted, ?_⟩
                  rcases parsed with limit | complete
                  · exact .inl limit
                  · exact .inr (by simpa only [alloc.vec.Vec.from_val, List.append_assoc, List.singleton_append] using complete)
                · simp [NativeM.fromRust, RustM.fail] at continuation
                  cases continuation
      · have notLess : ¬ accumulated.val.length < maxRecords.val := by
          simpa only [alloc.vec.Vec.len, UScalar.lt_equiv, Usize.ofNatCore,
            UScalar.ofNatCore_val_eq] using advance
        have equal : accumulated.val.length = maxRecords.val := by omega
        simp only [advance, ↓reduceIte, NativeM.ok, Result.ok_bind] at trace
        cases trace
        exact ⟨rfl, before, rfl, rfl, stable, valid, .inl equal⟩

omit heapLayout in
private theorem seek_zero_step (before : State) (offset : U64) (after : State)
    (stable : before.durable = before.visible)
    (step : seekStep before (.start 0#u64) = some (.Ok offset, after)) :
    ∃ rest, offset = 0#u64 ∧ after = sought before 0 before.visible rest := by
  unfold seekStep at step
  cases chosen : action "seek" before.script with
  | none => simp [chosen] at step
  | some choice =>
      obtain ⟨success, value, mask, rest⟩ := choice
      simp only [chosen, Option.bind_eq_bind, Option.bind_some] at step
      cases accepted : persist before.durable before.visible mask with
      | none => simp [accepted] at step
      | some bytes =>
          simp only [accepted, Option.bind_some] at step
          cases success
          · simp at step
          · have same := persist_same before.visible mask bytes (by simpa only [stable] using accepted)
            subst bytes
            simp only [↓reduceIte] at step
            split at step
            · contradiction
            · simp only [Option.some.injEq, Prod.mk.injEq, core.result.Result.Ok.injEq] at step
              obtain ⟨rfl, rfl⟩ := step
              exact ⟨rest, by apply UScalar.eq_of_val_eq; rfl, rfl⟩

/-- A successful actual initial seek retains file identity and the stable byte image. -/
theorem seek_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State)
    (offset : U64) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (trace : Result.ReadyPrefix (io_core.seek_to file 0#u64) (fileEnv env file before frame)
      (.ok ((core.result.Result.Ok offset : core.result.Result U64 NativeIoError), returnedFile)) world) :
    returnedFile = file ∧ ∃ rest, world = fileEnv env file (sought before 0 before.visible rest) frame := by
  simp only [io_core.seek_to, io_core.seek_from, Record.Extraction.FileModel.seek,
    NativeFile.seek, monadLift_self] at trace
  cases trace with
  | wait _ _ actual _ middle _ _ ready continuation =>
      cases actual with
      | error exception => cases continuation
      | ok output =>
          cases continuation
          unfold pollSeek at ready
          rw [lookup_at env file before frame separate valid] at ready
          by_cases stopped : blocked before = true
          · simp [stopped] at ready
          · simp only [stopped] at ready
            cases step : seekStep before (.start 0#u64) with
            | none => simp [step] at ready
            | some outcome =>
                obtain ⟨reply, after⟩ := outcome
                simp only [step] at ready
                obtain ⟨rfl, rfl⟩ := ready
                obtain ⟨rest, _, rfl⟩ := seek_zero_step before offset after stable step
                exact ⟨rfl, rest, store_at env file before _ frame separate⟩

/-- Successful completion of the actual cross-crate recovery scan on a stable
reopened image. Host choices and the initial cursor are arbitrary. The result
is either capped by the caller's limit or exactly the acknowledged records;
errors, blocking and exhaustion do not satisfy the successful-return premise. -/
theorem recover_returns (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before : State) (values : List U16) (tail : List U8)
    (maxRecords : Usize) (returned : alloc.vec.Vec U16) (returnedFile : NativeFile) (world : Environment)
    (separate : Separate file frame) (valid : Valid before) (stable : before.durable = before.visible)
    (contents : before.visible = disk (logBytes values ++ tail)) (short : tail.length < 4)
    (trace : Result.ReadyPrefix (recover_log file maxRecords) (fileEnv env file before frame)
      (.ok (.Ok returned, returnedFile)) world) :
    returnedFile = file ∧ ∃ after, world = fileEnv env file after frame ∧
      after.visible = before.visible ∧ after.durable = before.visible ∧ Valid after ∧
      (returned.val.length = maxRecords.val ∨ returned.val = values) := by
  simp only [recover_log, monadLift_self] at trace
  obtain ⟨seek, middle, seekTrace, continuation⟩ := trace.bind_returns
  obtain ⟨reply, soughtFile⟩ := seek
  cases reply with
  | Err error =>
      simp only [NativeM.ok] at continuation
      cases continuation
  | Ok offset =>
      obtain ⟨fileEqual, rest, rfl⟩ := seek_returns file env frame before offset soughtFile middle
        separate valid stable seekTrace
      subst soughtFile
      simp only [recover_log_loop, NativeM.loop, monadLift_self] at continuation
      have resetValid : Valid (sought before 0 before.visible rest) :=
        ⟨valid.1, le_rfl, by simp [sought, limit]⟩
      have bytes : (sought before 0 before.visible rest).visible.data.toList.drop
          (sought before 0 before.visible rest).position = (logBytes values ++ tail).map rawByte := by
        simp [sought, contents, disk]
      simpa only [sought, alloc.vec.Vec.new, alloc.vec.Vec.from_val, List.nil_append] using
        loop_returns file env frame (sought before 0 before.visible rest) values tail
          (alloc.vec.Vec.new U16) maxRecords _ returned returnedFile world separate resetValid rfl
          bytes short (by simp [alloc.vec.Vec.new]) continuation

end Record.RepairReturnProperties
