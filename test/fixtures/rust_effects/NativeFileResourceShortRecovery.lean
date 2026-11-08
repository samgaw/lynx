module
public import FileResource.RecordRecovery
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.ShortRecovery
open NativeFile
open FileResource.Recovery (one path_bytes)

@[expose] def raw (contents : List U8) : ByteArray :=
  ⟨(contents.map fun byte => UInt8.ofNat byte.val).toArray⟩
@[expose] def closeScript (contents : List U8) : Term :=
  Recovery.actionOk "close" (Publish.zeroMask (raw contents)) .nil
@[expose] def reads (contents : List U8) : List U8 → Term
  | [] => .cons (.tuple #[.atom "read",.atom "ok",.integer 0,
      .bitstring (Publish.zeroMask (raw contents)) 0]) (closeScript contents)
  | _ :: rest => .cons (.tuple #[.atom "read",.atom "ok",.integer 1,
      .bitstring (Publish.zeroMask (raw contents)) 0]) (reads contents rest)
@[expose] def openingScript (contents : List U8) : Term :=
  .cons (.tuple #[.atom "open",.bitstring Creation.path 0,.atom "ok",.integer 0,reads contents contents]) .nil
@[expose] def boot (contents : List U8) (generation : Nat) : Environment :=
  {nativeRefCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],openingScript contents⟩),
    (1,inodeTypeName,encode ⟨raw contents,raw contents,0,.nil⟩)]}
@[expose] def scan (contents : List U8) (generation position : Nat) (script : Term)
    (closed : Bool := false) : Environment :=
  {nativeRefCounter := generation + 1,nativeHeap := [
    (generation + 1,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],.nil⟩),
    (1,inodeTypeName,encode ⟨raw contents,raw contents,0,.nil⟩)]}

theorem raw_size (contents : List U8) : (raw contents).size = contents.length := by
  simp [raw,← ByteArray.size_data]

theorem stable (contents : List U8) :
    persist (raw contents) (raw contents) (Publish.zeroMask (raw contents)) = some (raw contents) := by
  have conditions : (raw contents).size ≤ (Publish.zeroMask (raw contents)).size ∧
      (Publish.zeroMask (raw contents)).size ≤ (raw contents).size ∧
      ((Publish.zeroMask (raw contents)).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [Publish.zeroMask,← ByteArray.size_data]
  let result : ByteArray := ⟨(Publish.zeroMask (raw contents)).data.mapIdx fun index choice =>
    if choice == 1 then (raw contents)[index]! else (raw contents)[index]!⟩
  have accepted : persist (raw contents) (raw contents) (Publish.zeroMask (raw contents)) = some result := by
    unfold persist
    simp only [Nat.min_self,Nat.max_self]
    rw [ite_eq_left conditions]
  rw [Publish.persist_equal_images _ _ result accepted] at accepted
  exact accepted

theorem open_poll (contents : List U8) (short : contents.length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    pollOpenReadOnly (toStr "resource") (boot contents generation) =
      some (.ok (.Ok ⟨generation + 1⟩),scan contents generation 0 (reads contents contents)) := by
  have genNonzero : generation ≠ 0 := by omega
  have bound : ¬ 1048576 < (raw contents).size := by rw [raw_size]; omega
  simp [List.filter_nil,genNonzero,not_lt.mpr validGeneration,pollOpenReadOnly,path_bytes,
    supportedOpenPath,Publish.valid_path,boot,scan,openingScript,Publish.names,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,bound,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,handleTypeName]
  decide +kernel

theorem read_poll (front : List U8) (byte : U8) (rest : List U8)
    (short : (front ++ byte :: rest).length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    pollRead ⟨generation + 1⟩ (one 0#u8)
      (scan (front ++ byte :: rest) generation front.length (reads (front ++ byte :: rest) (byte :: rest))) =
      some (.ok (.Ok 1#usize,⟨generation + 1⟩,one byte),
        scan (front ++ byte :: rest) generation (front.length + 1) (reads (front ++ byte :: rest) rest)) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have dataBound : ¬ 1048576 < (raw (front ++ byte :: rest)).size := by rw [raw_size]; omega
  have positionBound : ¬ 1048576 < front.length := by simp only [List.length_append,List.length_cons] at short; omega
  have combinedBound : ¬ 1048576 < front.length + (rest.length + 1) := by
    simp only [List.length_append,List.length_cons] at short; omega
  have nonnegative : ¬ (front.length : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  simp [combinedBound,List.filter_cons,List.filter_nil,genNonzero,insideId,pollRead,lookup,sharedLookup,
    getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,positionBound,
    nonnegative,raw_size,blocked,readStep,readBuffer,reads,action,
    stable,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,store,sharedStore,typeName,
    handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]
  all_goals simp [raw]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem eof_poll (contents : List U8) (short : contents.length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    pollRead ⟨generation + 1⟩ (one 0#u8)
      (scan contents generation contents.length (reads contents [])) =
      some (.ok (.Ok 0#usize,⟨generation + 1⟩,one 0#u8),
        scan contents generation contents.length (closeScript contents)) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have dataBound : ¬ 1048576 < (raw contents).size := by rw [raw_size]; omega
  have positionBound : ¬ 1048576 < contents.length := by omega
  have nonnegative : ¬ (contents.length : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  simp [List.filter_cons,List.filter_nil,genNonzero,insideId,pollRead,lookup,sharedLookup,
    getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,positionBound,
    nonnegative,raw_size,blocked,readStep,readBuffer,reads,closeScript,Recovery.actionOk,action,
    stable,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,store,sharedStore,typeName,
    handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]
  all_goals constructor
  all_goals rfl

theorem close_poll (contents : List U8) (short : contents.length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    pollClose ⟨generation + 1⟩ (scan contents generation contents.length (closeScript contents)) =
      some (.ok (),scan contents generation contents.length .nil true) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have dataBound : ¬ 1048576 < (raw contents).size := by rw [raw_size]; omega
  have positionBound : ¬ 1048576 < contents.length := by omega
  have nonnegative : ¬ (contents.length : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  simp [List.filter_cons,List.filter_nil,genNonzero,insideId,pollClose,lookup,sharedLookup,
    getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,positionBound,
    nonnegative,raw_size,blocked,closeStep,closeScript,Recovery.actionOk,action,stable,
    sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]

/-- The actual word reader rejects EOF in its first byte and retains its caller. -/
theorem word_empty_next (contents : List U8) (short : contents.length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan contents generation contents.length (reads contents [])) =
    next (.Ok none,⟨generation + 1⟩) (scan contents generation contents.length (closeScript contents)) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (eof_poll contents short generation validGeneration)]
  simp [NativeM.ok]

/-- EOF in the second byte also returns no word after the first actual read. -/
theorem word_one_next (front : List U8) (byte : U8) (short : (front ++ [byte]).length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan (front ++ [byte]) generation front.length (reads (front ++ [byte]) [byte])) =
    next (.Ok none,⟨generation + 1⟩)
      (scan (front ++ [byte]) generation (front.length + 1) (closeScript (front ++ [byte]))) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (read_poll front byte [] short generation validGeneration)]
  simp only [bind_assoc,NativeM.ok,UScalar.ofNatCore_val_eq]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  have eof := eof_poll (front ++ [byte]) short generation validGeneration
  simp only [List.length_append,List.length_singleton] at eof
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ eof]
  simp []

/-- Two actual reads reconstruct the word before continuing with the remaining input. -/
theorem word_two_next (front : List U8) (a b : U8) (rest : List U8)
    (short : (front ++ a :: b :: rest).length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan (front ++ a :: b :: rest) generation front.length (reads (front ++ a :: b :: rest) (a :: b :: rest))) =
    next (.Ok (some (Record.word a b)),⟨generation + 1⟩)
      (scan (front ++ a :: b :: rest) generation (front.length + 2) (reads (front ++ a :: b :: rest) rest)) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (read_poll front a (b :: rest) short generation validGeneration)]
  simp only [bind_assoc,NativeM.ok,UScalar.ofNatCore_val_eq]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  have second := read_poll (front ++ [a]) b rest (by simpa using short) generation validGeneration
  simp only [List.append_assoc,List.singleton_append,List.length_append,List.length_singleton,Nat.add_assoc] at second
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ second]
  simp [Record.word,Array.from_slice,one,Array.index_usize,
    NativeM.monadLift_eq,NativeM.fromRust,Result.ok_bind]

/-- Every incomplete record is rejected by the two actual word readers,
including the second-word EOF branches. -/
theorem record_next (contents : List U8) (short : contents.length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_record ⟨generation + 1⟩ >>= next)
      (scan contents generation 0 (reads contents contents)) =
    next (.Ok none,⟨generation + 1⟩) (scan contents generation contents.length (closeScript contents)) := by
  cases contents with
  | nil =>
    simp only [effects_core.read_file_record,monadLift_self,bind_assoc]
    erw [word_empty_next [] short generation validGeneration]
    simp [NativeM.ok]
  | cons a tail =>
    cases tail with
    | nil =>
      simp only [effects_core.read_file_record,monadLift_self,bind_assoc]
      erw [word_one_next [] a short generation validGeneration]
      simp [NativeM.ok]
    | cons b tail =>
      cases tail with
      | nil =>
        simp only [effects_core.read_file_record,monadLift_self,bind_assoc]
        erw [word_two_next [] a b [] short generation validGeneration]
        simp only [NativeM.ok,bind_assoc]
        erw [word_empty_next [a,b] short generation validGeneration]
        simp []
      | cons c tail =>
        cases tail with
        | nil =>
          simp only [effects_core.read_file_record,monadLift_self,bind_assoc]
          erw [word_two_next [] a b [c] short generation validGeneration]
          simp only [NativeM.ok,bind_assoc]
          erw [word_one_next [a,b] c short generation validGeneration]
          simp []
        | cons d tail => simp at short; omega

/-- Actual owning recovery rejects incomplete records and closes its fresh descriptor. -/
theorem recover_short (contents : List U8) (short : contents.length < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    recover_file_record (toStr "resource") (boot contents generation) =
      (.ok (.Ok none),scan contents generation contents.length .nil true) := by
  simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll contents short generation validGeneration)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [record_next contents short generation validGeneration]
  simp only [NativeM.ok,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll contents short generation validGeneration)]
  simp []

@[expose] def contents (data : ByteArray) : List U8 := data.data.toList.map Recovery.byteValue

theorem contents_length (data : ByteArray) : (contents data).length = data.size := by
  simp [contents,← ByteArray.size_data]

theorem raw_contents (data : ByteArray) : raw (contents data) = data := by
  apply ByteArray.ext
  simp [raw,contents,List.map_map,Function.comp_def,Recovery.byteValue]

/-- The rejection property applies to every byte array of fewer than four bytes,
not just prefixes of a selected encoded value. -/
theorem recover_bytes (data : ByteArray) (short : data.size < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    recover_file_record (toStr "resource") (boot (contents data) generation) =
      (.ok (.Ok none),scan (contents data) generation data.size .nil true) := by
  simpa only [contents_length] using
    recover_short (contents data) (by simpa only [contents_length] using short) generation validGeneration

theorem restart_image (data : ByteArray) (short : data.size < 4)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    restartFilesystem ⟨Publish.names,[(1,data)],generation⟩ (openingScript (contents data)) =
      some (boot (contents data) generation) := by
  have bound : ¬ 1048576 < data.size := by omega
  simp [restartFilesystem,boot,raw_contents,namespaceTable,namespaceEntry,encodeNames,Publish.names,
    List.eraseDups_cons,Publish.valid_path,limit,bound,not_lt.mpr validGeneration]

/-- Actual resource writing composes with every admitted truncated-image choice
and the actual rejecting recovery implementation after restart. -/
theorem uncommitted_short_recovery (env : Environment) (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data) (short : data.size < 4) :
    filesystemCrashImage Publish.names [(1,mask)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨Publish.names,[(1,data)],7⟩ ∧
    restartFilesystem ⟨Publish.names,[(1,data)],7⟩ (openingScript (contents data)) =
      some (boot (contents data) 7) ∧
    recover_file_record (toStr "resource") (boot (contents data) 7) =
      (.ok (.Ok none),scan (contents data) 7 data.size .nil true) := by
  exact ⟨RecordRecovery.write_image_of_persist env value mask data accepted,
    restart_image data short 7 (by decide +kernel),recover_bytes data short 7 (by decide +kernel)⟩

@[expose] def missingChoice (error : Nat) : Term :=
  .cons (.tuple #[.atom "open",.bitstring Creation.path 0,.atom "error",.integer error,.nil]) .nil
@[expose] def missingBoot (data : ByteArray) (generation error : Nat) : Environment :=
  {nativeRefCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨[],[],[],missingChoice error⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩)]}
@[expose] def missingDone (data : ByteArray) (generation : Nat) : Environment :=
  {nativeRefCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨[],[],[],.nil⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩)]}

theorem missing_poll (data : ByteArray) (generation error : Nat) :
    pollOpenReadOnly (toStr "resource") (missingBoot data generation error) =
      some (.ok (.Err ⟨error⟩),missingDone data generation) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  simp [pollOpenReadOnly,path_bytes,supportedOpenPath,Publish.valid_path,missingBoot,missingDone,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,encodeNamespace,encodeNames,
    tablesEqual,openChoice,pathChoice,missingChoice,nonnegative,replaceNamespaceScript]

/-- A missing-name opening error is propagated by the actual Rust question-mark
path, without allocating, reading or closing a nonexistent file descriptor. -/
theorem missing_recovery (data : ByteArray) (generation error : Nat) :
    recover_file_record (toStr "resource") (missingBoot data generation error) =
      (.ok (.Err ⟨error⟩),missingDone data generation) := by
  simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (missing_poll data generation error)]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    NativeM.monadLift_eq,NativeM.fromRust,NativeM.ok]

theorem fresh_image_size (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data) : data.size ≤ 4 := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    have bound : mask.size ≤ 4 := by
      have bounded := conditions.2.1
      rw [Record.content_size] at bounded
      simpa [← ByteArray.size_data] using bounded
    cases accepted
    simpa [← ByteArray.size_data] using bound
  · contradiction

/-- Unsynchronized creation may lose the name while retaining the orphan inode. -/
theorem absent_image_of_persist (env : Environment) (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data) :
    filesystemCrashImage [] [(1,mask)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨[],[(1,data)],7⟩ := by
  simp [filesystemCrashImage,CreatedCalls.pinnedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,
    Record.written,Publish.namespaceBefore,Publish.names,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,Publish.valid_path,inode,decode,encode,Record.content_size,
    limit,accepted,inodeTypeName,namespaceTypeName,writableHandleTypeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName]

theorem missing_restart (data : ByteArray) (bound : data.size ≤ limit)
    (generation : Nat) (validGeneration : 1 ≤ generation) (error : Nat) :
    restartFilesystem ⟨[],[(1,data)],generation⟩ (missingChoice error) = some (missingBoot data generation error) := by
  simp [restartFilesystem,missingBoot,namespaceTable,encodeNames,List.eraseDups_cons,not_lt.mpr bound,not_lt.mpr validGeneration]

/-- Every admitted retained-orphan image with a lost name composes with actual
opening-error propagation under the declared failed-open OS outcome. -/
theorem uncommitted_missing_recovery (env : Environment) (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data) (error : Nat) :
    filesystemCrashImage [] [(1,mask)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨[],[(1,data)],7⟩ ∧
    restartFilesystem ⟨[],[(1,data)],7⟩ (missingChoice error) = some (missingBoot data 7 error) ∧
    recover_file_record (toStr "resource") (missingBoot data 7 error) =
      (.ok (.Err ⟨error⟩),missingDone data 7) := by
  have bound : data.size ≤ limit := by have := fresh_image_size value mask data accepted; simp only [limit]; omega
  exact ⟨absent_image_of_persist env value mask data accepted,
    missing_restart data bound 7 (by decide +kernel) error,missing_recovery data 7 error⟩

@[expose] def zeroBytes (length : Nat) : ByteArray := ⟨_root_.Array.replicate length 0⟩

theorem persist_zero_fresh (value : U16) (length : Nat) (short : length < 4) :
    persist ByteArray.empty (Record.content value) (zeroBytes length) = some (zeroBytes length) := by
  unfold persist
  rw [Record.content_size]
  interval_cases length <;>
    simp [zeroBytes,← ByteArray.size_data]
  all_goals rfl

/-- Every short length has an admitted image and actual rejecting recovery,
without assumed admission or a substituted parser. -/
theorem short_witness (env : Environment) (value : U16) (length : Nat) (short : length < 4) :
    filesystemCrashImage Publish.names [(1,zeroBytes length)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨Publish.names,[(1,zeroBytes length)],7⟩ ∧
    restartFilesystem ⟨Publish.names,[(1,zeroBytes length)],7⟩ (openingScript (contents (zeroBytes length))) =
      some (boot (contents (zeroBytes length)) 7) ∧
    recover_file_record (toStr "resource") (boot (contents (zeroBytes length)) 7) =
      (.ok (.Ok none),scan (contents (zeroBytes length)) 7 (zeroBytes length).size .nil true) := by
  exact uncommitted_short_recovery env value _ _ (persist_zero_fresh value length short)
    (by simpa [zeroBytes,← ByteArray.size_data] using short)

private theorem bit_choice (byte : UInt8) (allowed : byte = 0 ∨ byte = 1) :
    ∃ bit : Bool, byte = if bit then 1 else 0 := by
  rcases allowed with rfl | rfl
  · exact ⟨false,rfl⟩
  · exact ⟨true,rfl⟩

/-- Every admitted complete-length mask belongs to the checked zero/new family;
this does not select a favorable subset of complete images. -/
theorem complete_mask (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data)
    (full : data.size = 4) :
    ∃ x y z w : Bool, mask = RecordRecovery.tearingMask x y z w ∧
      data = RecordRecovery.tornData value x y z w := by
  have conditions : min ByteArray.empty.size (Record.content value).size ≤ mask.size ∧
      mask.size ≤ max ByteArray.empty.size (Record.content value).size ∧
      mask.data.toList.all (fun byte => byte == 0 || byte == 1) = true := by
    unfold persist at accepted
    split at accepted
    · assumption
    · contradiction
  have length : data.size = mask.size := by
    unfold persist at accepted
    split at accepted
    · cases accepted; simp [← ByteArray.size_data]
    · contradiction
  have listLength : mask.data.toList.length = 4 := by
    simpa [← ByteArray.size_data] using length.symm.trans full
  obtain ⟨a,b,c,d,shape⟩ : ∃ a b c d : UInt8, mask.data.toList = [a,b,c,d] := by
    exact ⟨_,_,_,_,List.eq_getElem_of_length_eq_four _ listLength⟩
  have bits : (a = 0 ∨ a = 1) ∧ (b = 0 ∨ b = 1) ∧
      (c = 0 ∨ c = 1) ∧ (d = 0 ∨ d = 1) := by
    simpa [shape] using conditions.2.2
  obtain ⟨x,hx⟩ := bit_choice a bits.1
  obtain ⟨y,hy⟩ := bit_choice b bits.2.1
  obtain ⟨z,hz⟩ := bit_choice c bits.2.2.1
  obtain ⟨w,hw⟩ := bit_choice d bits.2.2.2
  have maskEq : mask = RecordRecovery.tearingMask x y z w := by
    apply ByteArray.ext
    have arrays := congrArg List.toArray shape
    simpa [RecordRecovery.tearingMask,hx,hy,hz,hw] using arrays
  have found := accepted
  rw [maskEq,RecordRecovery.persist_torn] at found
  exact ⟨x,y,z,w,maskEq,Option.some.inj found.symm⟩

/-- Persisted fresh-record bytes have a verified recovery for any valid restart
watermark, independently of the resource or directory phase that produced them. -/
theorem persisted_image_recovery (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data)
    (generation : Nat) (validGeneration : 1 ≤ generation) :
    ∃ script before after result,
      restartFilesystem ⟨Publish.names,[(1,data)],generation⟩ script = some before ∧
      recover_file_record (toStr "resource") before = (.ok (.Ok result),after) ∧
      (result = none ∨ result = some value) := by
  have bound := fresh_image_size value mask data accepted
  by_cases short : data.size < 4
  · exact ⟨openingScript (contents data),boot (contents data) generation,scan (contents data) generation data.size .nil true,
      none,
      restart_image data short generation validGeneration,recover_bytes data short generation validGeneration,Or.inl rfl⟩
  · have full : data.size = 4 := by omega
    obtain ⟨x,y,z,w,maskEq,dataEq⟩ := complete_mask value mask data accepted full
    let a := Record.selected x (Record.low value)
    let b := Record.selected y (Record.high value)
    let c := Record.selected z (Record.low (~~~value))
    let d := Record.selected w (Record.high (~~~value))
    have restarted : restartFilesystem ⟨Publish.names,[(1,data)],generation⟩ RecordRecovery.openingScript =
        some (RecordRecovery.boot a b c d generation) := by
      rw [dataEq]
      exact RecordRecovery.restart_image a b c d generation validGeneration
    have outcomes := RecordRecovery.torn_recovery value x y z w generation validGeneration
    change recover_file_record (toStr "resource") (RecordRecovery.boot a b c d generation) =
      (.ok (.Ok none),RecordRecovery.scan a b c d generation 4 .nil true) ∨
      recover_file_record (toStr "resource") (RecordRecovery.boot a b c d generation) =
      (.ok (.Ok (some value)),RecordRecovery.scan a b c d generation 4 .nil true) at outcomes
    rcases outcomes with rejected | recovered
    · exact ⟨RecordRecovery.openingScript,RecordRecovery.boot a b c d generation,
        RecordRecovery.scan a b c d generation 4 .nil true,none,
        restarted,rejected,Or.inl rfl⟩
    · exact ⟨RecordRecovery.openingScript,RecordRecovery.boot a b c d generation,
        RecordRecovery.scan a b c d generation 4 .nil true,some value,
        restarted,recovered,Or.inr rfl⟩

/-- Every admitted named image after the actual write has a consistent ready
recovery execution that rejects or returns the original value. -/
theorem named_image_recovery (env : Environment) (value : U16) (mask data : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some data) :
    ∃ script before after result,
      filesystemCrashImage Publish.names [(1,mask)]
        (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
        some ⟨Publish.names,[(1,data)],7⟩ ∧
      restartFilesystem ⟨Publish.names,[(1,data)],7⟩ script = some before ∧
      recover_file_record (toStr "resource") before = (.ok (.Ok result),after) ∧
      (result = none ∨ result = some value) := by
  obtain ⟨script,before,after,result,restarted,recovered,allowed⟩ :=
    persisted_image_recovery value mask data accepted 7 (by decide +kernel)
  exact ⟨script,before,after,result,RecordRecovery.write_image_of_persist env value mask data accepted,
    restarted,recovered,allowed⟩

private theorem pending_names (selected : Names)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed Publish.namespaceBefore selected = true) :
    selected = [] ∨ selected = Publish.names := by
  simp [namespaceCrashAllowed,Publish.namespaceBefore,Publish.names,namedInode] at allowed
  have mapped : selected.map (fun entry => entry.1.data) =
      List.replicate selected.length Creation.path.data := by
    apply List.map_eq_replicate_iff.mpr
    intro entry member
    exact (allowed.1 entry.1 entry.2 member).symm
  rw [mapped] at unique
  cases selected with
  | nil => exact Or.inl rfl
  | cons head tail =>
    have empty : tail = [] := by
      have length : tail.length = 0 := by
        simpa [List.replicate_succ,List.eraseDups_cons] using unique.symm
      exact List.eq_nil_of_length_eq_zero length
    subst tail
    have same : head.1 = Creation.path := by
      apply ByteArray.ext
      exact (allowed.1 head.1 head.2 (by simp)).symm
    cases head with
    | mk path id =>
      simp only at same
      subst path
      right
      simp at allowed
      simpa [Publish.names] using allowed

private theorem table_unique (chosen selected : Names)
    (table : namespaceTable (encodeNames chosen) = some selected) :
    (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length := by
  simp only [encodeNames,namespaceTable] at table
  split at table
  · contradiction
  · simp only [Bind.bind,Option.bind_eq_some_iff] at table
    rcases table with ⟨mapped,parsed,table⟩
    split at table
    · contradiction
    · rename_i unique
      cases table
      simpa using unique

private theorem written_namespace (env : Environment) (value : U16) :
    namespaceSnapshot (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some Publish.namespaceBefore := by
  simp [namespaceSnapshot,CreatedCalls.pinnedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,
    Publish.namespaceBefore,Publish.names,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,Publish.valid_path]

private theorem written_nodes (env : Environment) (value : U16) :
    (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore).nativeHeap.filter
      (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨Record.content value,ByteArray.empty,0,.nil⟩)] := by
  simp [CreatedCalls.pinnedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,Record.written,
    inodeTypeName,namespaceTypeName,writableHandleTypeName,NativeResourceArc.typeName,
    NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName]

private theorem written_inode (env : Environment) (value : U16) :
    inode 1 (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨Record.content value,ByteArray.empty,0,.nil⟩ := by
  simp [inode,CreatedCalls.pinnedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,Record.written,
    inodeTypeName,namespaceTypeName,writableHandleTypeName,NativeResourceArc.typeName,
    NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName,
    decode,encode,Record.content_size,limit]

/-- Exhaustive classification of admitted name/mask choices after writing:
only an absent or retained name and one bounded persisted inode are possible. -/
theorem write_crash_shape (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) = some image) :
    ∃ mask data, masks = [(1,mask)] ∧
      persist ByteArray.empty (Record.content value) mask = some data ∧
      image.inodes = [(1,data)] ∧ image.highWater = 7 ∧
      (image.names = [] ∨ image.names = Publish.names) := by
  simp only [filesystemCrashImage,written_namespace,Bind.bind,Option.bind_some,
    Option.bind_eq_some_iff] at accepted
  rcases accepted with ⟨selected,table,accepted⟩
  split at accepted
  · contradiction
  · rename_i allowed
    have choices := pending_names selected (table_unique chosen selected table) (by simpa using allowed)
    simp only [written_nodes,List.length_singleton,Nat.reduceGT] at accepted
    split at accepted
    · contradiction
    · rename_i keys
      have key_eq : masks.map (·.1) = [1] := by simpa using keys
      have shape : ∃ mask, masks = [(1,mask)] := by
        cases masks with
        | nil => simp at key_eq
        | cons head tail =>
          cases head with
          | mk id mask =>
            simp only [List.map_cons,List.cons.injEq,List.map_eq_nil_iff] at key_eq
            obtain ⟨rfl,rfl⟩ := key_eq
            exact ⟨mask,rfl⟩
      obtain ⟨mask,rfl⟩ := shape
      simp only [List.mapM_cons,List.mapM_nil,Option.bind_eq_some_iff,written_inode,Option.bind_some,
        List.filter_cons,List.filter_nil,Nat.reduceBEq,↓reduceIte] at accepted
      rcases accepted with ⟨images,mapped,accepted⟩
      cases saved : persist ByteArray.empty (Record.content value) mask with
      | none => simp [saved,Bind.bind] at mapped
      | some data =>
        have images_eq : images = [(1,data)] := by simpa [saved,Bind.bind,Pure.pure] using mapped.symm
        subst images
        split at accepted
        · contradiction
        · cases accepted
          exact ⟨mask,data,rfl,saved,rfl,rfl,choices⟩

/-- Exhaustive post-write image recovery: under consistent ready-read or failed-open
OS outcomes, every admitted name/length/byte choice rejects, reports the opening
error, or recovers the original value. No other value is accepted. -/
theorem all_image_recovery (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage) (error : Nat)
    (accepted : filesystemCrashImage chosen masks
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) = some image) :
    ∃ script before after result,
      restartFilesystem image script = some before ∧
      recover_file_record (toStr "resource") before = (.ok result,after) ∧
      (result = .Err ⟨error⟩ ∨ result = .Ok none ∨ result = .Ok (some value)) := by
  obtain ⟨mask,data,masksEq,persisted,inodes,water,names⟩ := write_crash_shape env value chosen masks image accepted
  rcases names with absent | retained
  · have imageEq : image = ⟨[],[(1,data)],7⟩ := by cases image; simp_all
    have bound : data.size ≤ limit := by have := fresh_image_size value mask data persisted; simp only [limit]; omega
    refine ⟨missingChoice error,missingBoot data 7 error,missingDone data 7,.Err ⟨error⟩,?_,
      missing_recovery data 7 error,Or.inl rfl⟩
    rw [imageEq]
    exact missing_restart data bound 7 (by decide +kernel) error
  · have imageEq : image = ⟨Publish.names,[(1,data)],7⟩ := by cases image; simp_all
    obtain ⟨script,before,after,result,captured,restarted,recovered,allowed⟩ :=
      named_image_recovery env value mask data persisted
    refine ⟨script,before,after,.Ok result,?_,recovered,Or.inr ?_⟩
    · rw [imageEq]
      exact restarted
    · rcases allowed with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl

@[expose] def partialBefore (count : Nat) : State :=
  ⟨ByteArray.empty,ByteArray.empty,0,Record.writeChoice count⟩
@[expose] def partialState (value : U16) (count : Nat) : State :=
  ⟨overwrite ByteArray.empty 0 (Record.content value) count,ByteArray.empty,count,CreatedCalls.syncChoice .nil⟩
@[expose] def writtenCount (count : Nat) (shortCount : count < 4) : Usize :=
  Usize.ofNatCore count (by scalar_tac)

theorem partial_size (value : U16) (count : Nat) (shortCount : count < 4) :
    (partialState value count).visible.size = count := by
  have contentLength : (Record.content value).data.toList.length = 4 := by
    simpa [← ByteArray.size_data] using Record.content_size value
  by_cases zero : count = 0
  · subst count; simp [partialState,overwrite,← ByteArray.size_data]
  · simp [partialState,overwrite,zero,← ByteArray.size_data,contentLength,Nat.min_eq_left (by omega : count ≤ 4)]

theorem partial_step (value : U16) (count : Nat) (shortCount : count < 4) :
    writeStep (partialBefore count) (Record.wire value) =
      some (.Ok (writtenCount count shortCount),partialState value count) := by
  have nonnegative : ¬ (count : Int) < 0 := not_lt.mpr (Int.natCast_nonneg count)
  have countBound : count ≤ 4 := by omega
  have limitBound : ¬ 1048576 < count := by omega
  simp [writeStep,partialBefore,partialState,Record.writeChoice,action,
    nonnegative,countBound,limit,limitBound,persist,← ByteArray.size_data,Record.content,Record.wire,writtenCount]
  rfl

theorem partial_valid (count : Nat) : CreatedCalls.Valid (partialBefore count) := by
  simp [CreatedCalls.Valid,partialBefore,limit,← ByteArray.size_data]

theorem short_flag (count : Nat) (shortCount : count < 4) :
    Rustler.encodeBool (writtenCount count shortCount = 4#usize) = Term.false := by
  have different : writtenCount count shortCount ≠ 4#usize := by
    intro equal
    have values := congrArg UScalar.val equal
    simp [writtenCount,UScalar.ofNatCore_val_eq] at values
    omega
  simp [Rustler.encodeBool,different]

/-- All supported short counts, including zero, are rejected by the actual NIF
while preserving their file effects and the live VM resource. -/
theorem create_partial (env : Environment) (value : U16) (count : Nat) (shortCount : count < 4)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool)
      (Creation.initial env (partialBefore count).script) =
      (.ok Term.false,CreatedCalls.pinnedEnv env (partialState value count) 7) := by
  rw [Creation.create_next (rest := .nil) env (partialBefore count).script _ registered]
  change (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool)
    (CreatedCalls.pinnedEnv env (partialBefore count) 6) = _
  have valid : CreatedCalls.Valid (partialBefore count) := by simp [CreatedCalls.Valid,partialBefore,limit,← ByteArray.size_data]
  have different : writtenCount count shortCount ≠ 4#usize := by
    intro equal
    have values := congrArg UScalar.val equal
    simp [writtenCount,UScalar.ofNatCore_val_eq] at values
    omega
  simpa [Result.bind_ok,Result.ok_apply,Rustler.encodeBool,different] using
    Record.write_next (ns := CreatedCalls.pendingNamespace) env (partialBefore count) (partialState value count) 6
      (by omega) valid rfl value (writtenCount count shortCount) (partial_step value count shortCount)
      Result.ok registered

theorem fresh_persist_size (visible mask data : ByteArray)
    (accepted : persist ByteArray.empty visible mask = some data) : data.size ≤ visible.size := by
  unfold persist at accepted
  split at accepted
  · rename_i conditions
    have bound : mask.size ≤ visible.size := by simpa [← ByteArray.size_data] using conditions.2.1
    cases accepted
    simpa [← ByteArray.size_data] using bound
  · contradiction

/-- A real short write's admitted named images retain its partial effects. -/
theorem partial_image (env : Environment) (value : U16) (count : Nat) (shortCount : count < 4) (keepName : Bool)
    (mask data : ByteArray)
    (accepted : persist ByteArray.empty (partialState value count).visible mask = some data) :
    filesystemCrashImage (if keepName then Publish.names else []) [(1,mask)]
      (CreatedCalls.pinnedEnv env (partialState value count) 7) =
      some ⟨(if keepName then Publish.names else []),[(1,data)],7⟩ := by
  have visibleSize : (overwrite ByteArray.empty 0 (Record.content value) count).size = count :=
    partial_size value count shortCount
  have bound : ¬ 1048576 < count := by omega
  simp only [partialState] at accepted
  cases keepName <;> simp [filesystemCrashImage,CreatedCalls.pinnedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,
    partialState,CreatedCalls.pendingNamespace,Publish.names,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,Publish.valid_path,inode,decode,encode,visibleSize,
    limit,bound,accepted,inodeTypeName,namespaceTypeName,writableHandleTypeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName]

/-- All admitted named images after any supported partial write are too short
for the actual record parser and are rejected after restart, with file cleanup. -/
theorem partial_write_recovery (env : Environment) (value : U16) (count : Nat) (shortCount : count < 4)
    (mask data : ByteArray)
    (accepted : persist ByteArray.empty (partialState value count).visible mask = some data) :
    filesystemCrashImage Publish.names [(1,mask)]
      (CreatedCalls.pinnedEnv env (partialState value count) 7) =
      some ⟨Publish.names,[(1,data)],7⟩ ∧
    restartFilesystem ⟨Publish.names,[(1,data)],7⟩ (openingScript (contents data)) =
      some (boot (contents data) 7) ∧
    recover_file_record (toStr "resource") (boot (contents data) 7) =
      (.ok (.Ok none),scan (contents data) 7 data.size .nil true) := by
  have bound := fresh_persist_size (partialState value count).visible mask data accepted
  have short : data.size < 4 := by rw [partial_size value count shortCount] at bound; omega
  exact ⟨partial_image env value count shortCount true mask data accepted,
    restart_image data short 7 (by decide +kernel),recover_bytes data short 7 (by decide +kernel)⟩

theorem partial_missing_recovery (env : Environment) (value : U16) (count : Nat) (shortCount : count < 4)
    (mask data : ByteArray)
    (accepted : persist ByteArray.empty (partialState value count).visible mask = some data) (error : Nat) :
    filesystemCrashImage [] [(1,mask)] (CreatedCalls.pinnedEnv env (partialState value count) 7) =
      some ⟨[],[(1,data)],7⟩ ∧
    restartFilesystem ⟨[],[(1,data)],7⟩ (missingChoice error) = some (missingBoot data 7 error) ∧
    recover_file_record (toStr "resource") (missingBoot data 7 error) =
      (.ok (.Err ⟨error⟩),missingDone data 7) := by
  have size := fresh_persist_size (partialState value count).visible mask data accepted
  have bound : data.size ≤ limit := by rw [partial_size value count shortCount] at size; simp only [limit]; omega
  exact ⟨partial_image env value count shortCount false mask data accepted,
    missing_restart data bound 7 (by decide +kernel) error,missing_recovery data 7 error⟩

@[expose] def seed : Environment := Creation.initial {} (partialBefore 3).script

theorem returned_before (env : Environment) (count : Nat) :
    Creation.returned env (partialBefore count).script =
      CreatedCalls.pinnedEnv env (partialBefore count) 6 := rfl

end FileResource.ShortRecovery
