module
public import Publish.WordRecovery
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.RepeatedRecovery
open NativeFile Publish.Properties
open Publish.WordRecovery (wordBytes word_size byteValue stable_bytes word word_roundtrip word_value lowByte highByte)
open Publish.NamedRecovery (one closeScript readChoice readScript openingScript)

theorem read_next {α : Type} (file : NativeFile) (env updated : Environment) (buffer output : Slice U8)
    (reply : core.result.Result Usize NativeIoError)
    (ready : pollRead file buffer env = some (.ok (reply,file,output),updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (io_core.read_once file buffer >>= next) env = next (reply,file,output) updated := by
  simp only [io_core.read_once,monadLift_self,NativeFile.read,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

variable (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation)

@[expose] def boot : Environment :=
  {nativeRefCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],openingScript⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
@[expose] def scan (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {nativeRefCounter := generation + 1,nativeHeap := [
    (generation + 1,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
include validGeneration

theorem open_poll : pollOpenReadOnly target (boot low high generation) = some (.ok (.Ok ⟨generation + 1⟩),scan low high generation 0 readScript)  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,pollOpenReadOnly,target_bytes,supportedOpenPath,valid_b,boot,scan,openingScript,
    readScript,readChoice,closeScript,actionOk,newNames,word_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,
    handleTypeName]

theorem first_poll : pollRead ⟨generation + 1⟩ (one 0#u8) (scan low high generation 0 readScript) =
    some (.ok (.Ok 1#usize,⟨generation + 1⟩,one (byteValue low)),scan low high generation 1 (readChoice closeScript))  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readScript,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,wordBytes,byteValue,Data.ListN.ListN.from_to_inverse]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem second_poll : pollRead ⟨generation + 1⟩ (one 0#u8) (scan low high generation 1 (readChoice closeScript)) =
    some (.ok (.Ok 1#usize,⟨generation + 1⟩,one (byteValue high)),scan low high generation 2 closeScript)  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,wordBytes,byteValue,Data.ListN.ListN.from_to_inverse]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem close_poll : pollClose ⟨generation + 1⟩ (scan low high generation 2 closeScript) = some (.ok (),scan low high generation 2 .nil true)  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,closeStep,closeScript,actionOk,action,
    stable_bytes,sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

/-- The actual parser reads both bytes from the shared named inode. -/
theorem parsed_word : read_word ⟨generation + 1⟩ (scan low high generation 0 readScript) =
    (.ok (.Ok (some (word low high)),⟨generation + 1⟩),scan low high generation 2 closeScript)  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change (io_core.read_once ⟨generation + 1⟩ (one 0#u8) >>= _).run _ = _
  rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (first_poll low high generation validGeneration)]
  change (io_core.read_once ⟨generation + 1⟩ (one 0#u8) >>= _).run _ = _
  rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (second_poll low high generation validGeneration)]
  simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,word,NativeM.ok,NativeM.lift,Array.from_slice,Array.to_slice_mut,
    one,Array.make_val,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
    Result.ok_bind,Result.ok_apply]

/-- Composes Rust parsing with actual destruction of its owned handle. -/
theorem parse_and_close : read_and_close_word ⟨generation + 1⟩ (scan low high generation 0 readScript) =
    (.ok (.Ok (some (word low high))),scan low high generation 2 .nil true)  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have parser {α : Type} (next : _ → NativeM α) :
      (read_word ⟨generation + 1⟩ >>= next) (scan low high generation 0 readScript) =
        next (.Ok (some (word low high)),⟨generation + 1⟩) (scan low high generation 2 closeScript)  := by
    simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
      Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
    change (io_core.read_once ⟨generation + 1⟩ (one 0#u8) >>= _).run _ = _
    rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (first_poll low high generation validGeneration)]
    simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,bind_assoc]
    change (io_core.read_once ⟨generation + 1⟩ (one 0#u8) >>= _).run _ = _
    rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (second_poll low high generation validGeneration)]
    simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,word,NativeM.ok,NativeM.lift,Array.from_slice,Array.to_slice_mut,
      one,Array.make_val,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
      Result.ok_bind,Result.ok_apply]
  simp only [read_and_close_word,monadLift_self]
  rw [parser]
  simp only [NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll low high generation validGeneration)]
  simp [List.filter_cons,List.filter_nil,Payload.not_directory,genNonzero,Ne.symm nonzero,not_lt.mpr validGeneration,validGeneration,different,Ne.symm different,nonzero,inside,NativeM.ok]

/-- Opening, decoding and scope cleanup use extracted first-party Rust code. -/
theorem recover_word : recover_named_word target (boot low high generation) =
    (.ok (.Ok (some (word low high))),scan low high generation 2 .nil true)  := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp only [recover_named_word,io_core.open_readonly,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll low high generation validGeneration)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  exact parse_and_close low high generation validGeneration



/-- The actual owning recovery computation reaches this state after opening
and one read. Its remaining parser/cleanup computation is retained explicitly. -/
theorem recovery_prefix : ∃ residual,
    Result.ReadyPrefix (recover_named_word target) (boot low high generation)
      residual (scan low high generation 1 (readChoice closeScript)) := by
  simp only [recover_named_word,io_core.open_readonly,monadLift_self,openReadOnly,Result.wait_bind]
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (open_poll low high generation validGeneration)
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,read_and_close_word,read_word,
    NativeM.lift,monadLift_self,Array.to_slice_mut,Array.to_slice,Array.make_val,
    bind_assoc,io_core.read_once,NativeFile.read,Result.wait_bind]
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (first_poll low high generation validGeneration)
  exact ⟨_,.refl _ _⟩

/-- A read or close does not change these already synchronized inode bytes.
Crash image selection discards the volatile cursor and capability. -/
theorem captured_image (position : Nat) (script : Term) (closed : Bool) (mask result : ByteArray)
    (accepted : persist (wordBytes low high) (wordBytes low high) mask = some result) :
    filesystemCrashImage newNames [(1,mask)] (scan low high generation position script closed) =
      some ⟨newNames,[(1,wordBytes low high)],generation + 1⟩ := by
  have different : generation + 1 ≠ 1 := by omega
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have same := persist_same _ mask result accepted
  subst result
  cases closed <;>
    simp [genNonzero,List.filter_cons,List.filter_nil,filesystemCrashImage,scan,namespaceSnapshot,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
      namespaceCrashAllowed,namedInode,newNames,valid_b,word_size,inode,decode,encode,
      encodeHandle,limit,accepted,inside,different,Ne.symm different,
      inodeTypeName,namespaceTypeName,closedHandleTypeName,handleTypeName]

theorem restart_image :
    restartFilesystem ⟨newNames,[(1,wordBytes low high)],generation + 1⟩ openingScript =
      some (boot low high (generation + 1)) := by
  have inside : ¬ generation + 1 < 1 := by omega
  simp [restartFilesystem,boot,namespaceTable,namespaceEntry,encodeNames,newNames,
    List.eraseDups_cons,valid_b,word_size,limit,inside,namespaceTypeName,inodeTypeName]

/-- Interrupt the actual recovery after its first read, select any admitted
persistent image, restart, and recover the same complete word with a fresh handle. -/
theorem interrupted_recovery (mask result : ByteArray)
    (accepted : persist (wordBytes low high) (wordBytes low high) mask = some result) :
    (∃ residual, Result.ReadyPrefix (recover_named_word target) (boot low high generation)
      residual (scan low high generation 1 (readChoice closeScript))) ∧
    filesystemCrashImage newNames [(1,mask)]
      (scan low high generation 1 (readChoice closeScript)) =
        some ⟨newNames,[(1,wordBytes low high)],generation + 1⟩ ∧
    restartFilesystem ⟨newNames,[(1,wordBytes low high)],generation + 1⟩ openingScript =
      some (boot low high (generation + 1)) ∧
    recover_named_word target (boot low high (generation + 1)) =
      (.ok (.Ok (some (word low high))),scan low high (generation + 1) 2 .nil true) := by
  have nextValid : 1 ≤ generation + 1 := by omega
  exact ⟨recovery_prefix low high generation validGeneration,
    captured_image low high generation validGeneration 1 (readChoice closeScript) false mask result accepted,
    restart_image low high generation validGeneration,
    recover_word low high (generation + 1) nextValid⟩

/-- Successful recovery can itself be followed by another crash/restart and
successful recovery. Generation is arbitrary, so the result applies after any
previous number of completed or interrupted recovery attempts. -/
theorem repeated_recovery (mask result : ByteArray)
    (accepted : persist (wordBytes low high) (wordBytes low high) mask = some result) :
    recover_named_word target (boot low high generation) =
      (.ok (.Ok (some (word low high))),scan low high generation 2 .nil true) ∧
    filesystemCrashImage newNames [(1,mask)] (scan low high generation 2 .nil true) =
      some ⟨newNames,[(1,wordBytes low high)],generation + 1⟩ ∧
    restartFilesystem ⟨newNames,[(1,wordBytes low high)],generation + 1⟩ openingScript =
      some (boot low high (generation + 1)) ∧
    recover_named_word target (boot low high (generation + 1)) =
      (.ok (.Ok (some (word low high))),scan low high (generation + 1) 2 .nil true) := by
  have nextValid : 1 ≤ generation + 1 := by omega
  exact ⟨recover_word low high generation validGeneration,
    captured_image low high generation validGeneration 2 .nil true mask result accepted,
    restart_image low high generation validGeneration,
    recover_word low high (generation + 1) nextValid⟩

theorem recover_value (value : U16) :
    recover_named_word target (boot (lowByte value) (highByte value) generation) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) generation 2 .nil true) := by
  simpa only [word_roundtrip] using
    recover_word (lowByte value) (highByte value) generation validGeneration

theorem old_handle_gone :
    lookup ⟨generation + 1⟩ (boot low high (generation + 1)) = none := by
  have different : generation + 1 ≠ 1 := by omega
  have nonzero : generation + 1 ≠ 0 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [genNonzero,lookup,boot,List.filter_cons,different,Ne.symm different,nonzero,Ne.symm nonzero,
    namespaceTypeName,inodeTypeName,typeName,handleTypeName,writableHandleTypeName]

omit validGeneration in
/-- Actual publication, crash/restart, interruption of actual recovery after one
read, a second crash/restart and complete recovery compose for every u16 value. -/
theorem publication_interrupted (value : U16) (firstMask secondMask firstResult secondResult : ByteArray)
    (first : persist (wordBytes (lowByte value) (highByte value))
      (wordBytes (lowByte value) (highByte value)) firstMask = some firstResult)
    (second : persist (wordBytes (lowByte value) (highByte value))
      (wordBytes (lowByte value) (highByte value)) secondMask = some secondResult) :
    let low := lowByte value
    let high := highByte value
    let data := wordBytes low high
    publish_file ⟨2⟩ source target (Payload.initial data) = (.ok (.Ok ()),Payload.published data) ∧
    filesystemCrashImage newNames [(1,firstMask)] (Payload.published data) = some ⟨newNames,[(1,data)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,data)],3⟩ openingScript = some (boot low high 3) ∧
    (∃ residual, Result.ReadyPrefix (recover_named_word target) (boot low high 3)
      residual (scan low high 3 1 (readChoice closeScript))) ∧
    filesystemCrashImage newNames [(1,secondMask)] (scan low high 3 1 (readChoice closeScript)) =
      some ⟨newNames,[(1,data)],4⟩ ∧
    restartFilesystem ⟨newNames,[(1,data)],4⟩ openingScript = some (boot low high 4) ∧
    recover_named_word target (boot low high 4) = (.ok (.Ok (some value)),scan low high 4 2 .nil true) := by
  have published := Publish.WordRecovery.publish_value value firstMask firstResult first
  have interrupted := interrupted_recovery (lowByte value) (highByte value) 3 (by decide) secondMask secondResult second
  refine ⟨published.1,published.2.1,?_,interrupted.1,interrupted.2.1,interrupted.2.2.1,?_⟩
  · rfl
  · simpa only [word_roundtrip] using interrupted.2.2.2

end Publish.RepeatedRecovery
