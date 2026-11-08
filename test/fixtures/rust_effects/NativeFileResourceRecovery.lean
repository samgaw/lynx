module
public import FileResource.Publish
public import Aeneas.Data.BitVec
public import Mathlib.Tactic.IntervalCases
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Recovery
open NativeFile

@[expose] def actionOk (operation : String) (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom operation,.atom "ok",.integer 0,.bitstring mask 0]) rest
@[expose] def closeScript : Term := actionOk "close" ⟨#[0,0]⟩ .nil
@[expose] def readChoice (rest : Term) : Term :=
  .cons (.tuple #[.atom "read",.atom "ok",.integer 1,.bitstring ⟨#[0,0]⟩ 0]) rest
@[expose] def readScript : Term := readChoice (readChoice closeScript)
@[expose] def openingScript (script : Term := readScript) : Term :=
  .cons (.tuple #[.atom "open",.bitstring Creation.path 0,.atom "ok",.integer 0,script]) .nil
@[expose] def one (byte : U8) : Slice U8 := Slice.from [byte] (by scalar_tac)

theorem path_bytes : bytes (toStr "resource") = Creation.path := by
  simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,Creation.path]
  all_goals decide +kernel

@[expose] def wordBytes (low high : UInt8) : ByteArray := ⟨#[low,high]⟩
@[expose] def byteValue (byte : UInt8) : U8 :=
  U8.ofNatCore byte.toNat (by have := byte.toNat_lt; scalar_tac)
@[expose] def word (low high : UInt8) : U16 :=
  core.num.U16.from_le_bytes (Array.make 2#usize [byteValue low,byteValue high])

variable (low high : UInt8)

theorem word_bv : (word low high).bv = (byteValue high).bv ++ (byteValue low).bv := by
  apply (BitVec.eq_iff _ _).mpr
  intro i hi
  simp only [word,core.num.U16.from_le_bytes,U16.bv,
    BitVec.getElem!_cast,BitVec.fromLEBytes_getElem!]
  change Byte.testBit (((Array.make 2#usize [byteValue low,byteValue high]).val.map U8.bv)[i / 8]!)
    (i % 8) = _
  rw [Array.make_val]
  interval_cases i <;> simp only [Nat.reduceDiv,Nat.reduceMod,List.map_cons,List.map_nil,
    List.getElem!_cons_zero,List.getElem!_cons_succ,BitVec.getElem!_eq_testBit_toNat] <;> bv_normalize

theorem word_value : (word low high).val = low.toNat + 256 * high.toNat := by
  change (word low high).bv.toNat = _
  rw [word_bv]
  change ((⟨high.toNat,high.toNat_lt⟩ : BitVec 8) ++ (⟨low.toNat,low.toNat_lt⟩ : BitVec 8)).toNat = _
  rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofFin]
  rw [← Nat.shiftLeft_add_eq_or_of_lt low.toNat_lt high.toNat,Nat.shiftLeft_eq]
  omega

theorem word_size : (wordBytes low high).size = 2 := rfl

theorem stable_bytes (low high : UInt8) :
    persist (wordBytes low high) (wordBytes low high) ⟨#[0,0]⟩ = some (wordBytes low high) := by
  rfl

variable (generation : Nat)

@[expose] def boot (script : Term := readScript) : Environment :=
  {refCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],openingScript script⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
@[expose] def scan (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {refCounter := generation + 1,nativeHeap := [
    (generation + 1,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],.nil⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
theorem open_poll (validGeneration : 1 ≤ generation) (script : Term := readScript) : pollOpenReadOnly (toStr "resource") (boot low high generation script) = some (.ok (.Ok ⟨generation + 1⟩),scan low high generation 0 script) := by
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_nil,genNonzero,not_lt.mpr validGeneration,pollOpenReadOnly,path_bytes,supportedOpenPath,Publish.valid_path,boot,scan,openingScript,
    Publish.names,word_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,
    handleTypeName]
  decide +kernel

theorem first_poll (validGeneration : 1 ≤ generation) : pollRead ⟨generation + 1⟩ (one 0#u8) (scan low high generation 0 readScript) =
    some (.ok (.Ok 1#usize,⟨generation + 1⟩,one (byteValue low)),scan low high generation 1 (readChoice closeScript)) := by
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,genNonzero,inside,pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readScript,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [wordBytes,byteValue]
  all_goals constructor
  all_goals rfl

theorem second_poll (validGeneration : 1 ≤ generation) : pollRead ⟨generation + 1⟩ (one 0#u8) (scan low high generation 1 (readChoice closeScript)) =
    some (.ok (.Ok 1#usize,⟨generation + 1⟩,one (byteValue high)),scan low high generation 2 closeScript) := by
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,genNonzero,inside,pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [wordBytes,byteValue]
  all_goals constructor
  all_goals rfl

theorem close_poll (validGeneration : 1 ≤ generation) (position : Nat) (bounded : position ≤ limit) : pollClose ⟨generation + 1⟩ (scan low high generation position closeScript) = some (.ok (),scan low high generation position .nil true) := by
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have nonnegative : ¬ (position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg position)
  have bound : ¬ 1048576 < position := by simpa [limit] using not_lt.mpr bounded
  simp [List.filter_cons,List.filter_nil,genNonzero,inside,nonnegative,bound,pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,closeStep,closeScript,actionOk,action,
    stable_bytes,sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem read_next {α : Type} (file : NativeFile) (env updated : Environment) (buffer output : Slice U8)
    (reply : core.result.Result Usize NativeIoError)
    (ready : pollRead file buffer env = some (.ok (reply,file,output),updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (effects_core.read_file_once file buffer >>= next) env = next (reply,file,output) updated := by
  simp only [effects_core.read_file_once,monadLift_self,NativeFile.read,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- The actual parser reads both bytes from the shared named inode. -/
theorem parsed_word (validGeneration : 1 ≤ generation) : effects_core.read_file_word ⟨generation + 1⟩ (scan low high generation 0 readScript) =
    (.ok (.Ok (some (word low high)),⟨generation + 1⟩),scan low high generation 2 closeScript) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (first_poll low high generation validGeneration)]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (second_poll low high generation validGeneration)]
  simp [word,NativeM.ok,Array.from_slice,
    one,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
    Result.ok_bind,Result.ok_apply]

@[expose] def lowByte (value : U16) : UInt8 := UInt8.ofNat (value.val % 256)
@[expose] def highByte (value : U16) : UInt8 := UInt8.ofNat (value.val / 256)

theorem word_roundtrip (value : U16) : word (lowByte value) (highByte value) = value := by
  apply UScalar.eq_of_val_eq
  rw [word_value]
  have bound : value.val < 65536 := by scalar_tac
  have highBound : value.val / 256 < 256 := by omega
  simp only [lowByte,highByte,UInt8.toNat_ofNat',Nat.reducePow,Nat.mod_mod,
    Nat.mod_eq_of_lt highBound]
  omega

theorem content_layout (value : U16) :
    Write.content value = wordBytes (lowByte value) (highByte value) := by
  simp only [Write.content,Write.wire,bytes,Array.val_to_slice,core.num.U16.to_le_bytes,
    Array.from_val,wordBytes,lowByte,highByte,UScalar.val]
  simp only [List.map_toArray,List.map_map]
  change (⟨((value.bv.toLEBytes.map fun x => UInt8.ofNat x.toNat).toArray)⟩ : ByteArray) = _
  rw [BitVec.toLEBytes]
  simp only [Nat.reduceGT,↓reduceIte]
  rw [BitVec.toLEBytes]
  simp only [Nat.reduceSub,Nat.reduceGT,↓reduceIte]
  rw [BitVec.toLEBytes]
  simp only [Nat.reduceGT,↓reduceIte,List.map_cons,List.map_nil]
  have bound : value.bv.toNat < 65536 := value.bv.isLt
  have highBound : value.bv.toNat / 256 < 256 := by omega
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,
    Nat.reducePow,Nat.mod_eq_of_lt highBound]


/-- Recovery reopens the persistent inode and closes its fresh descriptor. -/
theorem recover_word (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation) :
    recover_file_word (toStr "resource") (boot low high generation) =
      (.ok (.Ok (some (word low high))),scan low high generation 2 .nil true) := by
  have parser {α : Type} (next : _ → NativeM α) :
      (effects_core.read_file_word ⟨generation + 1⟩ >>= next) (scan low high generation 0 readScript) =
        next (.Ok (some (word low high)),⟨generation + 1⟩) (scan low high generation 2 closeScript) := by
    simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
      Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
    change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
    rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (first_poll low high generation validGeneration)]
    simp [bind_assoc]
    change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
    rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (second_poll low high generation validGeneration)]
    simp [word,NativeM.ok,Array.from_slice,
      one,Array.index_usize,NativeM.fromRust,
      Result.ok_bind]
  simp only [recover_file_word,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll low high generation validGeneration)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [parser]
  simp only [NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll low high generation validGeneration 2 (by decide +kernel))]
  simp [NativeM.ok]

theorem recover_value (value : U16) (generation : Nat) (validGeneration : 1 ≤ generation) :
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value) generation) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) generation 2 .nil true) := by
  simpa only [word_roundtrip] using recover_word (lowByte value) (highByte value) generation validGeneration

private theorem synchronized_names (selected : Names)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed (Publish.namespaceAfter true) selected = true) :
    selected = Publish.names := by
  simp [namespaceCrashAllowed,Publish.namespaceAfter,Publish.names,namedInode] at allowed
  have mapped : selected.map (fun entry => entry.1.data) =
      List.replicate selected.length Creation.path.data := by
    apply List.map_eq_replicate_iff.mpr
    intro entry member
    exact (allowed.1 entry.1 entry.2 member).symm
  rw [mapped] at unique
  rcases allowed.2 with ⟨actual,found⟩
  cases selected with
  | nil => simp at found
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
      simp at found
      simp [Publish.names,found]


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

/-- Every admitted post-acknowledgment image has the same persistent identity. -/
theorem crash_identity (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (Publish.done env value) = some image) :
    image = ⟨Publish.names,[(1,Write.content value)],9⟩ := by
  have contents := Publish.crash_contents env value chosen masks image accepted
  have identity : image.names = Publish.names ∧ image.highWater = 9 := by
    simp only [filesystemCrashImage,Publish.namespace_done,Bind.bind,Option.bind_some,
      Option.bind_eq_some_iff] at accepted
    rcases accepted with ⟨selected,table,accepted⟩
    split at accepted
    · contradiction
    · rename_i allowed
      have same := synchronized_names selected (table_unique chosen selected table) (by simpa using allowed)
      split at accepted
      · contradiction
      · simp only [Option.bind_eq_some_iff] at accepted
        rcases accepted with ⟨images,mapped,accepted⟩
        split at accepted
        · contradiction
        · cases accepted
          exact ⟨same,rfl⟩
  cases image
  simp_all

/-- Restart discards all prior capabilities and restores only persistent state. -/
theorem restart_image (value : U16) :
    restartFilesystem ⟨Publish.names,[(1,Write.content value)],9⟩ openingScript =
      some (boot (lowByte value) (highByte value) 9) := by
  rw [content_layout]
  rfl

/-- Actual recovery consumes every admitted crash image after the resource protocol. -/
theorem recover_admitted (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (Publish.done env value) = some image) :
    restartFilesystem image openingScript = some (boot (lowByte value) (highByte value) 9) ∧
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value) 9) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 9 2 .nil true) := by
  rw [crash_identity env value chosen masks image accepted]
  exact ⟨restart_image value,recover_value value 9 (by decide +kernel)⟩

/-- The complete actual resource protocol and internal recovery compose for all payloads. -/
theorem commit_recovery (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__WRITE__ owner value) Rustler.encodeBool
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) (Creation.initial env Write.before.script Publish.opening) =
      (.ok Term.true,Publish.done env value) ∧
    (∃ image, filesystemCrashImage Publish.names [(1,Publish.zeroMask (Write.content value))]
      (Publish.done env value) = some image) ∧
    (∀ chosen masks image, filesystemCrashImage chosen masks (Publish.done env value) = some image →
      restartFilesystem image openingScript = some (boot (lowByte value) (highByte value) 9) ∧
      recover_file_word (toStr "resource") (boot (lowByte value) (highByte value) 9) =
        (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 9 2 .nil true)) := by
  exact ⟨Publish.create_write_commit env value registered,
    ⟨_,Publish.admitted_crash env value⟩,recover_admitted env value⟩

@[expose] def readError (error : Nat) : Term :=
  .cons (.tuple #[.atom "read",.atom "error",.integer error,.bitstring ⟨#[0,0]⟩ 0]) closeScript

theorem error_poll (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation) (error : Nat) :
    pollRead ⟨generation + 1⟩ (one 0#u8) (scan low high generation 0 (readError error)) =
      some (.ok (.Err ⟨error⟩,⟨generation + 1⟩,one 0#u8),scan low high generation 0 closeScript) := by
  have inside : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  simp [List.filter_cons,List.filter_nil,genNonzero,inside,pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readError,closeScript,actionOk,
    action,nonnegative,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]

/-- The actual failed read returns its error and closes the newly opened file. -/
theorem read_error_cleanup (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation) (error : Nat) :
    recover_file_word (toStr "resource") (boot low high generation (readError error)) =
      (.ok (.Err ⟨error⟩),scan low high generation 0 .nil true) := by
  simp only [recover_file_word,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll low high generation validGeneration (readError error))]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [read_next ⟨generation + 1⟩ _ _ _ _ _ (error_poll low high generation validGeneration error)]
  simp only [NativeM.ok,Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll low high generation validGeneration 0 (by decide +kernel))]
  simp []

/-- Observable boundaries of the actual owning recovery computation. -/
inductive Phase where
  | beforeOpen | beforeFirstRead | beforeSecondRead | beforeClose | finished

@[expose] def phaseEnv (low high : UInt8) (generation : Nat) : Phase → Environment
  | .beforeOpen => boot low high generation
  | .beforeFirstRead => scan low high generation 0 readScript
  | .beforeSecondRead => scan low high generation 1 (readChoice closeScript)
  | .beforeClose => scan low high generation 2 closeScript
  | .finished => scan low high generation 2 .nil true

@[expose] def phaseWater (generation : Nat) : Phase → Nat
  | .beforeOpen => generation
  | _ => generation + 1

/-- Every declared crash boundary is reachable in the extracted computation;
its actual remaining parser and cleanup are retained as the residual. -/
theorem phase_prefix (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    ∃ residual, Result.ReadyPrefix (recover_file_word (toStr "resource"))
      (boot low high generation) residual (phaseEnv low high generation phase) := by
  cases phase <;> simp only [phaseEnv]
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [recover_file_word,monadLift_self,openReadOnly,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (open_poll low high generation validGeneration)
  · exact ⟨_,.refl _ _⟩
  all_goals simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok,effects_core.read_file_word,
    NativeM.lift,monadLift_self,Array.to_slice_mut,Array.to_slice,Array.make_val,
    bind_assoc,effects_core.read_file_once,NativeFile.read,Result.wait_bind]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (first_poll low high generation validGeneration)
  · exact ⟨_,.refl _ _⟩
  all_goals simp [bind_assoc]
  all_goals apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _ (second_poll low high generation validGeneration)
  · exact ⟨_,.refl _ _⟩
  simp [NativeM.ok,Array.from_slice,one,Array.index_usize,
    NativeM.fromRust,Result.ok_bind,
    NativeOwnedDrop.drop,close,Result.wait_bind]
  apply Result.ReadyPrefix.exists_wait _ _ _ _ _ _
    (close_poll low high generation validGeneration 2 (by decide +kernel))
  exact ⟨_,.refl _ _⟩

@[expose] def phaseScript : Phase → Term
  | .beforeOpen => openingScript
  | _ => .nil

private theorem phase_namespace (low high : UInt8) (generation : Nat)
    (phase : Phase) :
    namespaceSnapshot (phaseEnv low high generation phase) =
      some ⟨Publish.names,Publish.names,[],phaseScript phase⟩ := by
  cases phase <;>
    simp [phaseEnv,phaseScript,boot,scan,namespaceSnapshot,namespaceTable,namespaceHistory,
      namespaceEntry,encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,
      Publish.names,Publish.valid_path]

private theorem phase_inode (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    inode 1 (phaseEnv low high generation phase) =
      some ⟨wordBytes low high,wordBytes low high,0,.nil⟩ := by
  have inside : ¬ generation + 1 < 1 := by omega
  have genInside : ¬ generation < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  cases phase <;>
    simp [List.filter_nil,phaseEnv,boot,scan,inode,decode,encode,limit,word_size,
      inside,genInside,genNonzero]

private theorem phase_nodes (low high : UInt8) (generation : Nat) (phase : Phase) :
    (phaseEnv low high generation phase).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨wordBytes low high,wordBytes low high,0,.nil⟩)] := by
  cases phase <;> simp [phaseEnv,boot,scan,inodeTypeName,namespaceTypeName,
    handleTypeName,closedHandleTypeName]

/-- Every permitted crash at every actual recovery boundary preserves the
persistent name and bytes; volatile descriptors affect only freshness. -/
theorem phase_crash (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (phaseEnv low high generation phase) = some image) :
    image = ⟨Publish.names,[(1,wordBytes low high)],phaseWater generation phase⟩ := by
  simp only [filesystemCrashImage,phase_namespace low high generation,
    Bind.bind,Option.bind_some,Option.bind_eq_some_iff] at accepted
  rcases accepted with ⟨selected,table,accepted⟩
  split at accepted
  · contradiction
  · rename_i allowed
    have same := synchronized_names selected (table_unique chosen selected table) (by simpa [namespaceCrashAllowed,Publish.namespaceAfter] using allowed)
    subst selected
    simp only [phase_nodes,List.length_singleton,Nat.reduceGT] at accepted
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
      simp only [List.mapM_cons,List.mapM_nil,Option.bind_eq_some_iff,
        phase_inode low high generation validGeneration,Option.bind_some,
        List.filter_cons,List.filter_nil,Nat.reduceBEq,↓reduceIte] at accepted
      rcases accepted with ⟨images,mapped,accepted⟩
      cases saved : persist (wordBytes low high) (wordBytes low high) mask with
      | none => simp [saved,Bind.bind] at mapped
      | some bytes =>
        have fixed := Publish.persist_equal_images (wordBytes low high) mask bytes saved
        subst bytes
        have image_eq : images = [(1,wordBytes low high)] := by
          simpa [saved,Bind.bind,Pure.pure] using mapped.symm
        subst images
        split at accepted
        · contradiction
        · cases accepted
          cases phase <;> rfl

/-- Each boundary admits a concrete image; universal admission is not vacuous. -/
theorem phase_witness (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    filesystemCrashImage Publish.names [(1,⟨#[0,0]⟩)] (phaseEnv low high generation phase) =
      some ⟨Publish.names,[(1,wordBytes low high)],phaseWater generation phase⟩ := by
  simp only [filesystemCrashImage,phase_namespace low high generation,
    phase_nodes,Bind.bind,Option.bind_some]
  simp [Publish.names,namespaceTable,namespaceEntry,encodeNames,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,Publish.valid_path,
    phase_inode low high generation validGeneration,stable_bytes,Bind.bind]
  cases phase <;> rfl

theorem restart_checkpoint (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation) :
    restartFilesystem ⟨Publish.names,[(1,wordBytes low high)],generation⟩ openingScript =
      some (boot low high generation) := by
  simp [restartFilesystem,boot,namespaceTable,namespaceEntry,encodeNames,Publish.names,
    List.eraseDups_cons,Publish.valid_path,word_size,limit,not_lt.mpr validGeneration]

theorem phase_water_valid (generation : Nat) (validGeneration : 1 ≤ generation) (phase : Phase) :
    1 ≤ phaseWater generation phase ∧ generation ≤ phaseWater generation phase := by
  cases phase <;> simp [phaseWater]
  omega

/-- Crash/restart at an actual recovery boundary preserves the value and admits
complete recovery with fresh identity. This states safety and retry capability,
not fairness or eventual success under infinitely many crashes. -/
theorem phase_retry (value : U16) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks
      (phaseEnv (lowByte value) (highByte value) generation phase) = some image) :
    (∃ residual, Result.ReadyPrefix (recover_file_word (toStr "resource"))
      (boot (lowByte value) (highByte value) generation) residual
      (phaseEnv (lowByte value) (highByte value) generation phase)) ∧
    restartFilesystem image openingScript =
      some (boot (lowByte value) (highByte value) image.highWater) ∧
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value) image.highWater) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) image.highWater 2 .nil true) := by
  rw [phase_crash _ _ generation validGeneration phase chosen masks image accepted]
  have valid := (phase_water_valid generation validGeneration phase).1
  exact ⟨phase_prefix _ _ generation validGeneration phase,
    restart_checkpoint _ _ _ valid,recover_value value _ valid⟩

theorem old_handle_gone (low high : UInt8) (generation : Nat) (validGeneration : 1 ≤ generation) :
    lookup ⟨generation + 1⟩ (boot low high (generation + 1)) = none := by
  have genNonzero : generation ≠ 0 := by omega
  simp [genNonzero,lookup,boot,List.filter_nil,
    namespaceTypeName,inodeTypeName,
    ]

/-- Finite sequences of admitted crashes at the actual recovery boundaries.
The next freshness mark comes from the selected filesystem image. -/
inductive CrashRetries (low high : UInt8) : Nat → Nat → Prop where
  | done (generation : Nat) : CrashRetries low high generation generation
  | crash (generation : Nat) (phase : Phase) (chosen : Names)
      (masks : List (Nat × ByteArray)) (image : FilesystemImage) (finalGeneration : Nat)
      (accepted : filesystemCrashImage chosen masks (phaseEnv low high generation phase) = some image)
      (rest : CrashRetries low high image.highWater finalGeneration) :
      CrashRetries low high generation finalGeneration

/-- Induction covers any finite number of admitted completed or interrupted
recovery attempts, preserving freshness and the actual Rust recovery result. -/
theorem finite_retries (value : U16) (generation finalGeneration : Nat)
    (trace : CrashRetries (lowByte value) (highByte value) generation finalGeneration) :
    1 ≤ generation →
    1 ≤ finalGeneration ∧ generation ≤ finalGeneration ∧
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value) finalGeneration) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) finalGeneration 2 .nil true) := by
  induction trace with
  | done generation =>
    intro valid
    exact ⟨valid,Nat.le_refl _,recover_value value generation valid⟩
  | crash generation phase chosen masks image finalGeneration accepted rest ih =>
    intro valid
    have same := phase_crash _ _ generation valid phase chosen masks image accepted
    have progress : 1 ≤ image.highWater ∧ generation ≤ image.highWater := by
      rw [same]
      exact phase_water_valid generation valid phase
    rcases ih progress.1 with ⟨lastValid,ordered,recovered⟩
    exact ⟨lastValid,Nat.le_trans progress.2 ordered,recovered⟩

/-- Any boundary permits a nonempty finite retry trace without assuming
admission or a first-party implementation contract. -/
theorem nonempty_retry (value : U16) (generation : Nat) (validGeneration : 1 ≤ generation)
    (phase : Phase) :
    CrashRetries (lowByte value) (highByte value) generation (phaseWater generation phase) ∧
    recover_file_word (toStr "resource")
      (boot (lowByte value) (highByte value) (phaseWater generation phase)) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) (phaseWater generation phase) 2 .nil true) := by
  have trace : CrashRetries (lowByte value) (highByte value) generation (phaseWater generation phase) :=
    .crash generation phase Publish.names [(1,⟨#[0,0]⟩)]
      ⟨Publish.names,[(1,wordBytes (lowByte value) (highByte value))],phaseWater generation phase⟩ _
      (phase_witness _ _ generation validGeneration phase) (.done _)
  exact ⟨trace,(finite_retries value generation _ trace validGeneration).2.2⟩

/-- The resource protocol's admitted initial crash composes with any finite
sequence of further recovery crashes and the actual final recovery computation. -/
theorem committed_retries (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage) (finalGeneration : Nat)
    (accepted : filesystemCrashImage chosen masks (Publish.done env value) = some image)
    (trace : CrashRetries (lowByte value) (highByte value) image.highWater finalGeneration) :
    restartFilesystem image openingScript =
      some (boot (lowByte value) (highByte value) image.highWater) ∧
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value) finalGeneration) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) finalGeneration 2 .nil true) := by
  have same := crash_identity env value chosen masks image accepted
  have valid : 1 ≤ image.highWater := by rw [same]; change 1 ≤ 9; decide +kernel
  refine ⟨?_,(finite_retries value image.highWater finalGeneration trace valid).2.2⟩
  rw [same,content_layout]
  exact restart_checkpoint _ _ 9 (by decide +kernel)

end FileResource.Recovery
