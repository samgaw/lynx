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

@[expose] def boot (script : Term := readScript) : Environment :=
  {refCounter := 9,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],openingScript script⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
@[expose] def scan (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {refCounter := 10,nativeHeap := [
    (10,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],.nil⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
theorem open_poll (script : Term := readScript) : pollOpenReadOnly (toStr "resource") (boot low high script) = some (.ok (.Ok ⟨10⟩),scan low high 0 script) := by
  simp [pollOpenReadOnly,path_bytes,supportedOpenPath,Publish.valid_path,boot,scan,openingScript,
    Publish.names,word_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,
    handleTypeName]
  decide +kernel

theorem first_poll : pollRead ⟨10⟩ (one 0#u8) (scan low high 0 readScript) =
    some (.ok (.Ok 1#usize,⟨10⟩,one (byteValue low)),scan low high 1 (readChoice closeScript)) := by
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readScript,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [wordBytes,byteValue]
  all_goals constructor
  all_goals rfl

theorem second_poll : pollRead ⟨10⟩ (one 0#u8) (scan low high 1 (readChoice closeScript)) =
    some (.ok (.Ok 1#usize,⟨10⟩,one (byteValue high)),scan low high 2 closeScript) := by
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [wordBytes,byteValue]
  all_goals constructor
  all_goals rfl

theorem close_poll (position : Nat) (bounded : position ≤ limit) : pollClose ⟨10⟩ (scan low high position closeScript) = some (.ok (),scan low high position .nil true) := by
  have nonnegative : ¬ (position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg position)
  have bound : ¬ 1048576 < position := by simpa [limit] using not_lt.mpr bounded
  simp [nonnegative,bound,pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,closeStep,closeScript,actionOk,action,
    stable_bytes,sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem read_next {α : Type} (env updated : Environment) (buffer output : Slice U8)
    (reply : core.result.Result Usize NativeIoError)
    (ready : pollRead ⟨10⟩ buffer env = some (.ok (reply,⟨10⟩,output),updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (effects_core.read_file_once ⟨10⟩ buffer >>= next) env = next (reply,⟨10⟩,output) updated := by
  simp only [effects_core.read_file_once,monadLift_self,NativeFile.read,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ ready]
  simp

/-- The actual parser reads both bytes from the shared named inode. -/
theorem parsed_word : effects_core.read_file_word ⟨10⟩ (scan low high 0 readScript) =
    (.ok (.Ok (some (word low high)),⟨10⟩),scan low high 2 closeScript) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change (effects_core.read_file_once ⟨10⟩ (one 0#u8) >>= _) _ = _
  rw [read_next _ _ _ _ _ (first_poll low high)]
  change (effects_core.read_file_once ⟨10⟩ (one 0#u8) >>= _) _ = _
  rw [read_next _ _ _ _ _ (second_poll low high)]
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
theorem recover_word (low high : UInt8) :
    recover_file_word (toStr "resource") (boot low high) =
      (.ok (.Ok (some (word low high))),scan low high 2 .nil true) := by
  have parser {α : Type} (next : _ → NativeM α) :
      (effects_core.read_file_word ⟨10⟩ >>= next) (scan low high 0 readScript) =
        next (.Ok (some (word low high)),⟨10⟩) (scan low high 2 closeScript) := by
    simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
      Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
    change (effects_core.read_file_once ⟨10⟩ (one 0#u8) >>= _) _ = _
    rw [read_next _ _ _ _ _ (first_poll low high)]
    simp [bind_assoc]
    change (effects_core.read_file_once ⟨10⟩ (one 0#u8) >>= _) _ = _
    rw [read_next _ _ _ _ _ (second_poll low high)]
    simp [word,NativeM.ok,Array.from_slice,
      one,Array.index_usize,NativeM.fromRust,
      Result.ok_bind]
  simp only [recover_file_word,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll low high)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [parser]
  simp only [NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll low high 2 (by decide +kernel))]
  simp [NativeM.ok]

theorem recover_value (value : U16) :
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value)) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 2 .nil true) := by
  simpa only [word_roundtrip] using recover_word (lowByte value) (highByte value)

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
      some (boot (lowByte value) (highByte value)) := by
  rw [content_layout]
  rfl

/-- Actual recovery consumes every admitted crash image after the resource protocol. -/
theorem recover_admitted (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (Publish.done env value) = some image) :
    restartFilesystem image openingScript = some (boot (lowByte value) (highByte value)) ∧
    recover_file_word (toStr "resource") (boot (lowByte value) (highByte value)) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 2 .nil true) := by
  rw [crash_identity env value chosen masks image accepted]
  exact ⟨restart_image value,recover_value value⟩

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
      restartFilesystem image openingScript = some (boot (lowByte value) (highByte value)) ∧
      recover_file_word (toStr "resource") (boot (lowByte value) (highByte value)) =
        (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 2 .nil true)) := by
  exact ⟨Publish.create_write_commit env value registered,
    ⟨_,Publish.admitted_crash env value⟩,recover_admitted env value⟩

@[expose] def readError (error : Nat) : Term :=
  .cons (.tuple #[.atom "read",.atom "error",.integer error,.bitstring ⟨#[0,0]⟩ 0]) closeScript

theorem error_poll (low high : UInt8) (error : Nat) :
    pollRead ⟨10⟩ (one 0#u8) (scan low high 0 (readError error)) =
      some (.ok (.Err ⟨error⟩,⟨10⟩,one 0#u8),scan low high 0 closeScript) := by
  have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readError,closeScript,actionOk,
    action,nonnegative,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]

/-- The actual failed read returns its error and closes the newly opened file. -/
theorem read_error_cleanup (low high : UInt8) (error : Nat) :
    recover_file_word (toStr "resource") (boot low high (readError error)) =
      (.ok (.Err ⟨error⟩),scan low high 0 .nil true) := by
  simp only [recover_file_word,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll low high (readError error))]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨10⟩ (one 0#u8) >>= _) _ = _
  rw [read_next _ _ _ _ _ (error_poll low high error)]
  simp only [NativeM.ok,Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll low high 0 (by decide +kernel))]
  simp []

end FileResource.Recovery
