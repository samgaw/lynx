module
public import FileResource.Record
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.RecordRecovery
open NativeFile
open FileResource.Recovery (one path_bytes)

@[expose] def data (a b c d : U8) : ByteArray :=
  ⟨#[UInt8.ofNat a.val,UInt8.ofNat b.val,UInt8.ofNat c.val,UInt8.ofNat d.val]⟩
@[expose] def byteAt (a b c d : U8) : Nat → U8
  | 0 => a | 1 => b | 2 => c | _ => d
@[expose] def closeScript : Term := Recovery.actionOk "close" ⟨#[0,0,0,0]⟩ .nil
@[expose] def readScript : Nat → Term
  | 0 => closeScript
  | n + 1 => .cons (.tuple #[.atom "read",.atom "ok",.integer 1,.bitstring ⟨#[0,0,0,0]⟩ 0]) (readScript n)
@[expose] def openingScript : Term :=
  .cons (.tuple #[.atom "open",.bitstring Creation.path 0,.atom "ok",.integer 0,readScript 4]) .nil

variable (a b c d : U8) (generation : Nat)
@[expose] def boot : Environment :=
  {refCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],openingScript⟩),
    (1,inodeTypeName,encode ⟨data a b c d,data a b c d,0,.nil⟩)]}
@[expose] def scan (position : Nat) (script : Term) (closed : Bool := false) : Environment :=
  {refCounter := generation + 1,nativeHeap := [
    (generation + 1,(if closed then closedHandleTypeName else handleTypeName),encodeHandle ⟨1,position,script⟩),
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],.nil⟩),
    (1,inodeTypeName,encode ⟨data a b c d,data a b c d,0,.nil⟩)]}

theorem data_size : (data a b c d).size = 4 := rfl

theorem stable : persist (data a b c d) (data a b c d) ⟨#[0,0,0,0]⟩ = some (data a b c d) := by rfl

theorem open_poll (validGeneration : 1 ≤ generation) :
    pollOpenReadOnly (toStr "resource") (boot a b c d generation) =
      some (.ok (.Ok ⟨generation + 1⟩),scan a b c d generation 0 (readScript 4)) := by
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_nil,genNonzero,not_lt.mpr validGeneration,pollOpenReadOnly,path_bytes,
    supportedOpenPath,Publish.valid_path,boot,scan,openingScript,Publish.names,data_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,handleTypeName]
  decide +kernel

theorem read_poll (validGeneration : 1 ≤ generation) (position : Nat) (inside : position < 4) :
    pollRead ⟨generation + 1⟩ (one 0#u8) (scan a b c d generation position (readScript (4 - position))) =
      some (.ok (.Ok 1#usize,⟨generation + 1⟩,one (byteAt a b c d position)),
        scan a b c d generation (position + 1) (readScript (4 - (position + 1)))) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  interval_cases position <;>
    simp [List.filter_cons,List.filter_nil,genNonzero,insideId,pollRead,lookup,sharedLookup,
      getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,data_size,blocked,
      readStep,readBuffer,readScript,closeScript,Recovery.actionOk,action,stable,one,
      Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,store,sharedStore,typeName,
      handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]
  all_goals simp [data,byteAt]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem close_poll (validGeneration : 1 ≤ generation) :
    pollClose ⟨generation + 1⟩ (scan a b c d generation 4 closeScript) =
      some (.ok (),scan a b c d generation 4 .nil true) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_cons,List.filter_nil,genNonzero,insideId,pollClose,lookup,sharedLookup,
    getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,data_size,blocked,
    closeStep,closeScript,Recovery.actionOk,action,stable,sharedStore,retire,typeName,
    handleTypeName,writableHandleTypeName,closedHandleTypeName,inodeTypeName,namespaceTypeName]

theorem word_next (validGeneration : 1 ≤ generation) (position : Nat) (bounded : position + 1 < 4)
    {α : Type} (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan a b c d generation position (readScript (4 - position))) =
    next (.Ok (some (Record.word (byteAt a b c d position) (byteAt a b c d (position + 1)))),⟨generation + 1⟩)
      (scan a b c d generation (position + 2) (readScript (4 - (position + 2)))) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (read_poll a b c d generation validGeneration position (by omega))]
  simp only [bind_assoc,NativeM.ok,UScalar.ofNatCore_val_eq]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (read_poll a b c d generation validGeneration (position + 1) bounded)]
  simp [Record.word,Array.from_slice,one,Array.index_usize,
    NativeM.monadLift_eq,NativeM.fromRust,Result.ok_bind,Nat.add_assoc]

/-- Both actual word readers feed the actual Rust complement check. -/
theorem record_next (validGeneration : 1 ≤ generation) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_record ⟨generation + 1⟩ >>= next) (scan a b c d generation 0 (readScript 4)) =
    (effects_core.decode_record (Record.word a b) (Record.word c d) >>= fun found =>
      next (.Ok found,⟨generation + 1⟩)) (scan a b c d generation 4 closeScript) := by
  simp only [effects_core.read_file_record,monadLift_self,bind_assoc]
  rw [word_next a b c d generation validGeneration 0 (by decide +kernel)]
  simp only [byteAt,NativeM.ok,bind_assoc]
  rw [word_next a b c d generation validGeneration 2 (by decide +kernel)]
  simp [byteAt,readScript,bind_assoc]

/-- Opening, all four reads, integrity checking and closing are extracted Rust. -/
theorem recover_record (validGeneration : 1 ≤ generation) :
    recover_file_record (toStr "resource") (boot a b c d generation) =
      (.ok (.Ok (if Record.word a b ^^^ Record.word c d = core.num.U16.MAX then
        some (Record.word a b) else none)),scan a b c d generation 4 .nil true) := by
  simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll a b c d generation validGeneration)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [record_next a b c d generation validGeneration]
  simp only [Record.decode_spec,NativeM.ok,Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll a b c d generation validGeneration)]
  simp []

/-- A complete torn fresh record cannot be accepted as a different value. -/
theorem torn_recovery (value : U16) (x y z w : Bool) (generation : Nat) (validGeneration : 1 ≤ generation) :
    let a := Record.selected x (Record.low value)
    let b := Record.selected y (Record.high value)
    let c := Record.selected z (Record.low (~~~value))
    let d := Record.selected w (Record.high (~~~value))
    recover_file_record (toStr "resource") (boot a b c d generation) =
      (.ok (.Ok none),scan a b c d generation 4 .nil true) ∨
    recover_file_record (toStr "resource") (boot a b c d generation) =
      (.ok (.Ok (some value)),scan a b c d generation 4 .nil true) := by
  dsimp only
  have options := Record.torn_decode value x y z w
  simp only [Record.decode_spec,NativeM.ok,Result.ok.injEq] at options
  rcases options with rejected | accepted
  · left
    rw [recover_record _ _ _ _ generation validGeneration,rejected]
  · right
    rw [recover_record _ _ _ _ generation validGeneration,accepted]

theorem content_layout (value : U16) :
    Record.content value = data (Record.low value) (Record.high value)
      (Record.low (~~~value)) (Record.high (~~~value)) := by
  simp [Record.content,Record.wire,Record.layout,bytes,Array.make_val,Array.val_to_slice,data]

theorem recover_value (value : U16) (generation : Nat) (validGeneration : 1 ≤ generation) :
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value) (Record.low (~~~value)) (Record.high (~~~value)) generation) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) generation 4 .nil true) := by
  have accepted := Record.decode_layout value
  simp only [Record.decode_spec,NativeM.ok,Result.ok.injEq] at accepted
  rw [recover_record _ _ _ _ generation validGeneration,accepted]

theorem restart_image (validGeneration : 1 ≤ generation) :
    restartFilesystem ⟨Publish.names,[(1,data a b c d)],generation⟩ openingScript =
      some (boot a b c d generation) := by
  simp [restartFilesystem,boot,namespaceTable,namespaceEntry,encodeNames,Publish.names,
    List.eraseDups_cons,Publish.valid_path,data_size,limit,not_lt.mpr validGeneration]

@[expose] def tearingMask (x y z w : Bool) : ByteArray :=
  ⟨#[(if x then 1 else 0),(if y then 1 else 0),(if z then 1 else 0),(if w then 1 else 0)]⟩
@[expose] def tornData (value : U16) (x y z w : Bool) : ByteArray :=
  data (Record.selected x (Record.low value)) (Record.selected y (Record.high value))
    (Record.selected z (Record.low (~~~value))) (Record.selected w (Record.high (~~~value)))

theorem write_image_of_persist (env : Environment) (value : U16) (mask result : ByteArray)
    (accepted : persist ByteArray.empty (Record.content value) mask = some result) :
    filesystemCrashImage Publish.names [(1,mask)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨Publish.names,[(1,result)],7⟩ := by
  simp [filesystemCrashImage,CreatedCalls.pinnedEnv,NativeResourceArc.vmCells,CreatedCalls.frame,
    Record.written,Publish.namespaceBefore,Publish.names,namespaceSnapshot,namespaceTable,
    namespaceHistory,namespaceEntry,encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,
    namespaceCrashAllowed,namedInode,Publish.valid_path,inode,decode,encode,Record.content_size,
    limit,accepted,inodeTypeName,namespaceTypeName,writableHandleTypeName,
    NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeCodec.typeName]

theorem persist_torn (value : U16) (x y z w : Bool) :
    persist ByteArray.empty (Record.content value) (tearingMask x y z w) = some (tornData value x y z w) := by
  rw [content_layout]
  cases x <;> cases y <;> cases z <;> cases w <;>
    simp [tearingMask,tornData,Record.selected,data,persist,← ByteArray.size_data,getElem!_pos]
  all_goals
    repeat' apply And.intro
    all_goals rfl

/-- Every zero/new-byte pattern is an admitted complete-length image before fsync. -/
theorem written_image (env : Environment) (value : U16) (x y z w : Bool) :
    filesystemCrashImage Publish.names [(1,tearingMask x y z w)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨Publish.names,[(1,tornData value x y z w)],7⟩ := by
  exact write_image_of_persist env value _ _ (persist_torn value x y z w)

/-- The actual NIF may complete a whole write without making it durable. -/
theorem create_write (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool)
      (Creation.initial env Record.before.script Publish.opening) =
      (.ok Term.true,CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) := by
  rw [Creation.create_next (rest := Publish.opening) env Record.before.script _ registered,
    Record.returned_before]
  simpa [Result.bind_ok,Result.ok_apply,Rustler.encodeBool] using
    Record.write_next (ns := Publish.namespaceBefore) env Record.before (Record.written value) 6
      (by omega) Record.before_valid Record.before_ready value 4#usize (Record.full_step value)
      Result.ok registered

/-- Actual creation/write, an admitted torn crash, restart and actual checked
recovery cannot return a different value before commitment. -/
theorem uncommitted_write_recovery (env : Environment) (value : U16) (x y z w : Bool)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    let a := Record.selected x (Record.low value)
    let b := Record.selected y (Record.high value)
    let c := Record.selected z (Record.low (~~~value))
    let d := Record.selected w (Record.high (~~~value))
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool)
      (Creation.initial env Record.before.script Publish.opening) =
      (.ok Term.true,CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) ∧
    filesystemCrashImage Publish.names [(1,tearingMask x y z w)]
      (CreatedCalls.pinnedEnv env (Record.written value) 7 Publish.namespaceBefore) =
      some ⟨Publish.names,[(1,tornData value x y z w)],7⟩ ∧
    restartFilesystem ⟨Publish.names,[(1,tornData value x y z w)],7⟩ openingScript = some (boot a b c d 7) ∧
    (recover_file_record (toStr "resource") (boot a b c d 7) =
      (.ok (.Ok none),scan a b c d 7 4 .nil true) ∨
    recover_file_record (toStr "resource") (boot a b c d 7) =
      (.ok (.Ok (some value)),scan a b c d 7 4 .nil true)) := by
  dsimp only
  exact ⟨create_write env value registered,written_image env value x y z w,
    restart_image _ _ _ _ 7 (by decide +kernel),torn_recovery value x y z w 7 (by decide +kernel)⟩

end FileResource.RecordRecovery
