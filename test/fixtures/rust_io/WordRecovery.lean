module
public import Publish.Payload
public import Publish.NamedRecovery
public import Aeneas.Data.BitVec
public import Mathlib.Tactic.IntervalCases
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.WordRecovery
open NativeFile Publish.Properties
open Publish.NamedRecovery (one closeScript readChoice readScript openingScript read_next)

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

theorem stable_bytes : persist (wordBytes low high) (wordBytes low high) ⟨#[0,0]⟩ =
    some (wordBytes low high) := by
  have mask : Payload.zeroMask (wordBytes low high) = ⟨#[0,0]⟩ := by
    change (⟨_root_.Array.replicate 2 0⟩ : ByteArray) = ⟨#[0,0]⟩
    decide +kernel
  simpa only [mask] using Payload.persist_zero (wordBytes low high)

@[expose] def boot : Environment :=
  {nativeRefCounter := 3,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],openingScript⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
@[expose] def scan (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {nativeRefCounter := 4,nativeHeap := [
    (4,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨newNames,newNames,[],.nil⟩),
    (1,inodeTypeName,encode ⟨(wordBytes low high),(wordBytes low high),0,.nil⟩)]}
theorem open_poll : pollOpenReadOnly target (boot low high) = some (.ok (.Ok ⟨4⟩),scan low high 0 readScript) := by
  simp [pollOpenReadOnly,target_bytes,supportedOpenPath,valid_b,boot,scan,openingScript,
    readScript,readChoice,closeScript,actionOk,newNames,word_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,
    handleTypeName]
  decide +kernel

theorem first_poll : pollRead ⟨4⟩ (one 0#u8) (scan low high 0 readScript) =
    some (.ok (.Ok 1#usize,⟨4⟩,one (byteValue low)),scan low high 1 (readChoice closeScript)) := by
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readScript,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [wordBytes,byteValue,Data.ListN.ListN.from_to_inverse]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem second_poll : pollRead ⟨4⟩ (one 0#u8) (scan low high 1 (readChoice closeScript)) =
    some (.ok (.Ok 1#usize,⟨4⟩,one (byteValue high)),scan low high 2 closeScript) := by
  simp [pollRead,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,readStep,readBuffer,readChoice,
    closeScript,actionOk,action,stable_bytes,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]
  all_goals simp [wordBytes,byteValue,Data.ListN.ListN.from_to_inverse]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem close_poll : pollClose ⟨4⟩ (scan low high 2 closeScript) = some (.ok (),scan low high 2 .nil true) := by
  simp [pollClose,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,scan,inode,
    decode,encode,limit,word_size,blocked,closeStep,closeScript,actionOk,action,
    stable_bytes,sharedStore,retire,typeName,handleTypeName,writableHandleTypeName,
    closedHandleTypeName,inodeTypeName,namespaceTypeName]

/-- The actual parser reads both bytes from the shared named inode. -/
theorem parsed_word : read_word ⟨4⟩ (scan low high 0 readScript) =
    (.ok (.Ok (some (word low high)),⟨4⟩),scan low high 2 closeScript) := by
  simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val]
  change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _).run _ = _
  rw [read_next _ _ _ _ _ (first_poll low high)]
  change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _).run _ = _
  rw [read_next _ _ _ _ _ (second_poll low high)]
  simp [word,NativeM.ok,NativeM.lift,Array.from_slice,Array.to_slice_mut,
    one,Array.make_val,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
    Result.ok_bind,Result.ok_apply]

/-- Composes Rust parsing with actual destruction of its owned handle. -/
theorem parse_and_close : read_and_close_word ⟨4⟩ (scan low high 0 readScript) =
    (.ok (.Ok (some (word low high))),scan low high 2 .nil true) := by
  have parser {α : Type} (next : _ → NativeM α) :
      (read_word ⟨4⟩ >>= next).run (scan low high 0 readScript) =
        next (.Ok (some (word low high)),⟨4⟩) (scan low high 2 closeScript) := by
    simp only [read_word,NativeM.lift,monadLift_self,Result.ok_bind,
      Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
    change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _).run _ = _
    rw [read_next _ _ _ _ _ (first_poll low high)]
    simp [bind_assoc]
    change (io_core.read_once ⟨4⟩ (one 0#u8) >>= _).run _ = _
    rw [read_next _ _ _ _ _ (second_poll low high)]
    simp [word,NativeM.ok,NativeM.lift,Array.from_slice,Array.to_slice_mut,
      one,Array.make_val,Array.index_usize,NativeM.monadLift_eq,NativeM.fromRust,
      Result.ok_bind,Result.ok_apply]
  simp only [read_and_close_word,monadLift_self]
  rw [parser]
  simp only [NativeOwnedDrop.drop,close,Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ (close_poll low high)]
  simp [NativeM.ok]

/-- Opening, decoding and scope cleanup use extracted first-party Rust code. -/
theorem recover_word : recover_named_word target (boot low high) =
    (.ok (.Ok (some (word low high))),scan low high 2 .nil true) := by
  simp only [recover_named_word,io_core.open_readonly,monadLift_self,openReadOnly,Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ (open_poll low high)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  exact parse_and_close low high


/-- Publication and parsed recovery compose for every pair of bytes and every
admitted post-sync persistence mask, with the ordinary little-endian value. -/
theorem publication_recovery (mask result : ByteArray)
    (accepted : persist (wordBytes low high) (wordBytes low high) mask = some result) :
    publish_file ⟨2⟩ source target (Payload.initial (wordBytes low high)) =
      (.ok (.Ok ()),Payload.published (wordBytes low high)) ∧
    filesystemCrashImage newNames [(1,mask)] (Payload.published (wordBytes low high)) =
      some ⟨newNames,[(1,wordBytes low high)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,wordBytes low high)],3⟩ openingScript = some (boot low high) ∧
    recover_named_word target (boot low high) =
      (.ok (.Ok (some (word low high))),scan low high 2 .nil true) ∧
    (word low high).val = low.toNat + 256 * high.toNat := by
  have bound : (wordBytes low high).size ≤ limit := by rw [word_size]; decide +kernel
  refine ⟨Payload.publish_contract _ bound,Payload.checkpoint_image_all _ bound mask result accepted,
    ?_,recover_word low high,word_value low high⟩
  rfl

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

/-- The owning Rust recovery implementation returns every representable u16,
not just selected example values. -/
theorem recover_value (value : U16) :
    recover_named_word target (boot (lowByte value) (highByte value)) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 2 .nil true) := by
  simpa only [word_roundtrip] using recover_word (lowByte value) (highByte value)

/-- All u16 values survive actual publication, an admitted crash image, restart
and the owning Rust recovery implementation. -/
theorem publish_value (value : U16) (mask result : ByteArray)
    (accepted : persist (wordBytes (lowByte value) (highByte value))
      (wordBytes (lowByte value) (highByte value)) mask = some result) :
    let data := wordBytes (lowByte value) (highByte value)
    publish_file ⟨2⟩ source target (Payload.initial data) = (.ok (.Ok ()),Payload.published data) ∧
    filesystemCrashImage newNames [(1,mask)] (Payload.published data) = some ⟨newNames,[(1,data)],3⟩ ∧
    restartFilesystem ⟨newNames,[(1,data)],3⟩ openingScript =
      some (boot (lowByte value) (highByte value)) ∧
    recover_named_word target (boot (lowByte value) (highByte value)) =
      (.ok (.Ok (some value)),scan (lowByte value) (highByte value) 2 .nil true) := by
  have composed := publication_recovery (lowByte value) (highByte value) mask result accepted
  exact ⟨composed.1,composed.2.1,composed.2.2.1,recover_value value⟩

end Publish.WordRecovery
