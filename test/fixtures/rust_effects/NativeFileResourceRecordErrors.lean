module
public import FileResource.RecordRetry
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.RecordErrors
open NativeFile FileResource.RecordRecovery
open FileResource.Recovery (one path_bytes)

@[expose] def successRead (rest : Term) : Term :=
  .cons (.tuple #[.atom "read",.atom "ok",.integer 1,.bitstring ⟨#[0,0,0,0]⟩ 0]) rest
@[expose] def failedRead (error : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom "read",.atom "error",.integer error,.bitstring ⟨#[0,0,0,0]⟩ 0]) rest
@[expose] def closing : Option Nat → Term
  | none => closeScript
  | some error => .cons (.tuple #[.atom "close",.atom "error",.integer error,
      .bitstring ⟨#[0,0,0,0]⟩ 0]) .nil
@[expose] def reads (error : Nat) (rest : Term) : Nat → Term
  | 0 => failedRead error rest
  | n + 1 => successRead (reads error rest n)
@[expose] def opening (script : Term) : Term :=
  .cons (.tuple #[.atom "open",.bitstring Creation.path 0,.atom "ok",.integer 0,script]) .nil
@[expose] def boot (a b c d : U8) (generation : Nat) (script : Term) : Environment :=
  {refCounter := generation,nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨Publish.names,Publish.names,[],opening script⟩),
    (1,inodeTypeName,encode ⟨data a b c d,data a b c d,0,.nil⟩)]}

variable (a b c d : U8) (generation : Nat) (validGeneration : 1 ≤ generation)
include validGeneration

theorem open_poll (script : Term) :
    pollOpenReadOnly (toStr "resource") (boot a b c d generation script) =
      some (.ok (.Ok ⟨generation + 1⟩),scan a b c d generation 0 script) := by
  have genNonzero : generation ≠ 0 := by omega
  simp [List.filter_nil,genNonzero,not_lt.mpr validGeneration,pollOpenReadOnly,path_bytes,
    supportedOpenPath,Publish.valid_path,boot,scan,opening,Publish.names,data_size,
    namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,inode,
    decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,inodeTypeName,handleTypeName]
  decide +kernel

theorem success_poll (position : Nat) (inside : position < 4) (rest : Term) :
    pollRead ⟨generation + 1⟩ (one 0#u8)
      (scan a b c d generation position (successRead rest)) =
      some (.ok (.Ok 1#usize,⟨generation + 1⟩,one (byteAt a b c d position)),
        scan a b c d generation (position + 1) rest) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  interval_cases position <;>
    simp [List.filter_cons,List.filter_nil,genNonzero,insideId,pollRead,lookup,sharedLookup,
      getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,data_size,blocked,
      readStep,readBuffer,successRead,action,stable,one,
      Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,store,sharedStore,typeName,
      handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]
  all_goals simp [data,byteAt]
  all_goals constructor
  all_goals first | rfl | scalar_tac | (apply Slice.ext; simp [Slice.val,Data.ListN.ListN.from_to_inverse]; rfl)

theorem error_poll (position error : Nat) (bounded : position ≤ 4) (rest : Term) :
    pollRead ⟨generation + 1⟩ (one 0#u8)
      (scan a b c d generation position (failedRead error rest)) =
      some (.ok (.Err ⟨error⟩,⟨generation + 1⟩,one 0#u8),
        scan a b c d generation position rest) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have bound : ¬ 1048576 < position := by omega
  have nonnegative (n : Nat) : ¬ (n : Int) < 0 := by omega
  simp [bound,nonnegative,List.filter_cons,List.filter_nil,genNonzero,insideId,pollRead,lookup,sharedLookup,
    getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,data_size,blocked,
    readStep,failedRead,action,stable,one,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,
    store,sharedStore,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem close_poll (position : Nat) (bounded : position ≤ 4) (closeError : Option Nat) :
    pollClose ⟨generation + 1⟩ (scan a b c d generation position (closing closeError)) =
      some (.ok (),scan a b c d generation position .nil true) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have bound : ¬ 1048576 < position := by omega
  have nonnegative (n : Nat) : ¬ (n : Int) < 0 := by omega
  cases closeError <;>
    simp [bound,nonnegative,List.filter_cons,List.filter_nil,genNonzero,insideId,pollClose,lookup,sharedLookup,
      getHandle,decodeHandle,encodeHandle,scan,inode,decode,encode,limit,data_size,blocked,
      closeStep,closing,closeScript,Recovery.actionOk,action,stable,sharedStore,retire,typeName,
      handleTypeName,writableHandleTypeName,closedHandleTypeName,inodeTypeName,namespaceTypeName]

/-- A failed first read propagates its exact I/O error and retains the cursor. -/
theorem word_error_first (position error : Nat) (bounded : position ≤ 4) (rest : Term) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan a b c d generation position (failedRead error rest)) =
    next (.Err ⟨error⟩,⟨generation + 1⟩) (scan a b c d generation position rest) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (error_poll a b c d generation validGeneration position error bounded rest)]
  simp [NativeM.ok]

theorem word_error_second (position error : Nat) (inside : position < 4) (rest : Term) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan a b c d generation position (successRead (failedRead error rest))) =
    next (.Err ⟨error⟩,⟨generation + 1⟩) (scan a b c d generation (position + 1) rest) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (success_poll a b c d generation validGeneration position inside _)]
  simp only [bind_assoc,NativeM.ok,UScalar.ofNatCore_val_eq]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (error_poll a b c d generation validGeneration (position + 1) error (by omega) rest)]
  simp []

theorem word_next (position : Nat) (bounded : position + 1 < 4) (rest : Term) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_word ⟨generation + 1⟩ >>= next)
      (scan a b c d generation position (successRead (successRead rest))) =
    next (.Ok (some (Record.word (byteAt a b c d position) (byteAt a b c d (position + 1)))),⟨generation + 1⟩)
      (scan a b c d generation (position + 2) rest) := by
  simp only [effects_core.read_file_word,NativeM.lift,monadLift_self,Result.ok_bind,
    Array.to_slice_mut,Array.to_slice,Array.make_val,bind_assoc]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (success_poll a b c d generation validGeneration position (by omega) _)]
  simp only [bind_assoc,NativeM.ok,UScalar.ofNatCore_val_eq]
  change (effects_core.read_file_once ⟨generation + 1⟩ (one 0#u8) >>= _) _ = _
  rw [Recovery.read_next ⟨generation + 1⟩ _ _ _ _ _ (success_poll a b c d generation validGeneration (position + 1) bounded _)]
  simp [Record.word,Array.from_slice,one,Array.index_usize,
    NativeM.monadLift_eq,NativeM.fromRust,Result.ok_bind,Nat.add_assoc]

/-- Every one of the four read positions preserves the selected error; successful
preceding reads remain observable through the final cursor. -/
theorem record_error (position error : Nat) (inside : position < 4) (rest : Term) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_record ⟨generation + 1⟩ >>= next)
      (scan a b c d generation 0 (reads error rest position)) =
    next (.Err ⟨error⟩,⟨generation + 1⟩) (scan a b c d generation position rest) := by
  interval_cases position <;> simp only [effects_core.read_file_record,monadLift_self,bind_assoc,reads]
  · rw [word_error_first a b c d generation validGeneration _ _ (by omega)]
    simp [NativeM.ok]
  · rw [word_error_second a b c d generation validGeneration 0 error (by decide +kernel)]
    simp [NativeM.ok]
  all_goals rw [word_next a b c d generation validGeneration 0 (by decide +kernel)]
  all_goals simp only [NativeM.ok,bind_assoc]
  · rw [word_error_first a b c d generation validGeneration _ _ (by omega)]
    rfl
  · rw [word_error_second a b c d generation validGeneration 2 error (by decide +kernel)]
    rfl

/-- Actual owning recovery propagates every selected read error and destroys the
file on all ordinary returns, even when close itself reports an error. -/
theorem recover_error (position error : Nat) (inside : position < 4) (closeError : Option Nat) :
    recover_file_record (toStr "resource")
      (boot a b c d generation (reads error (closing closeError) position)) =
      (.ok (.Err ⟨error⟩),scan a b c d generation position .nil true) := by
  simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll a b c d generation validGeneration _)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [record_error a b c d generation validGeneration position error inside]
  simp only [NativeM.ok,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll a b c d generation validGeneration position (by omega) closeError)]
  simp []

@[expose] def completeRead (rest : Term) : Term :=
  successRead (successRead (successRead (successRead rest)))

/-- Successful reads retain the actual complement checker before continuation. -/
theorem record_next (rest : Term) {α : Type}
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (effects_core.read_file_record ⟨generation + 1⟩ >>= next)
      (scan a b c d generation 0 (completeRead rest)) =
    (effects_core.decode_record (Record.word a b) (Record.word c d) >>= fun found =>
      next (.Ok found,⟨generation + 1⟩)) (scan a b c d generation 4 rest) := by
  simp only [effects_core.read_file_record,monadLift_self,bind_assoc,completeRead]
  rw [word_next a b c d generation validGeneration 0 (by decide +kernel)]
  simp only [byteAt,NativeM.ok,bind_assoc]
  rw [word_next a b c d generation validGeneration 2 (by decide +kernel)]
  simp [byteAt,bind_assoc]

/-- The destructor cannot overwrite successful reads or integrity rejection with
its own close error under the stated std/OS destruction model. -/
theorem recover_complete (closeError : Option Nat) :
    recover_file_record (toStr "resource")
      (boot a b c d generation (completeRead (closing closeError))) =
      (.ok (.Ok (if Record.word a b ^^^ Record.word c d = core.num.U16.MAX then
        some (Record.word a b) else none)),scan a b c d generation 4 .nil true) := by
  simp only [recover_file_record,monadLift_self,openReadOnly,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (open_poll a b c d generation validGeneration _)]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  rw [record_next a b c d generation validGeneration]
  simp only [Record.decode_spec,NativeM.ok,Result.ok_bind,NativeOwnedDrop.drop,close,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ (close_poll a b c d generation validGeneration 4 (by decide +kernel) closeError)]
  simp []

/-- Restart retains the selected I/O outcomes while rebuilding fresh ownership. -/
theorem restart_image (script : Term) :
    restartFilesystem ⟨Publish.names,[(1,data a b c d)],generation⟩ (opening script) =
      some (boot a b c d generation script) := by
  simp [restartFilesystem,boot,opening,namespaceTable,namespaceEntry,encodeNames,Publish.names,
    List.eraseDups_cons,Publish.valid_path,data_size,limit,not_lt.mpr validGeneration]

omit validGeneration in
/-- Every admitted acknowledged image can encounter a read failure without
silently accepting data or losing the modeled destruction of its descriptor. -/
theorem committed_error (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (accepted : filesystemCrashImage chosen masks (Record.done env value) = some image)
    (position error : Nat) (inside : position < 4) (closeError : Option Nat) :
    restartFilesystem image (opening (reads error (closing closeError) position)) =
      some (boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) image.highWater (reads error (closing closeError) position)) ∧
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) image.highWater (reads error (closing closeError) position)) =
      (.ok (.Err ⟨error⟩),scan (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) image.highWater position .nil true) := by
  have same := RecordRetry.committed_crash env value chosen masks image accepted
  have valid : 1 ≤ image.highWater := by rw [same]; change 1 ≤ 9; decide +kernel
  refine ⟨?_,recover_error _ _ _ _ image.highWater valid position error inside closeError⟩
  rw [same,content_layout]
  exact restart_image _ _ _ _ 9 (by decide +kernel) _

/-- Closed descriptor cursors are volatile: their positions do not alter any
permitted filesystem crash image. This is equality of the declared OS model. -/
private theorem closed_crash_eq (position : Nat) (chosen : Names)
    (masks : List (Nat × ByteArray)) :
    filesystemCrashImage chosen masks (scan a b c d generation position .nil true) =
    filesystemCrashImage chosen masks (scan a b c d generation 4 .nil true) := by
  have insideId : ¬ generation + 1 < 1 := by omega
  have genNonzero : generation ≠ 0 := by omega
  have nodes (cursor : Nat) :
      (scan a b c d generation cursor .nil true).nativeHeap.filter (fun cell => cell.2.1 == inodeTypeName) =
      [(1,inodeTypeName,encode ⟨data a b c d,data a b c d,0,.nil⟩)] := by
    simp [scan,inodeTypeName,namespaceTypeName,closedHandleTypeName]
  simp only [filesystemCrashImage,nodes]
  simp [List.filter_cons,List.filter_nil,scan,namespaceSnapshot,namespaceTable,namespaceHistory,
    namespaceEntry,encodeNamespace,encodeNames,List.eraseDups_cons,tablesEqual,
    Publish.names,Publish.valid_path,inode,decode,encode,limit,data_size,
    insideId,genNonzero,inodeTypeName,namespaceTypeName,closedHandleTypeName]

omit validGeneration in
/-- A failed recovery closes its file. Any admitted subsequent crash retains the
acknowledged record, and any finite ready crash/retry trace can recover its value. -/
theorem error_then_retries (value : U16) (generation : Nat) (valid : 1 ≤ generation)
    (position error : Nat) (inside : position < 4) (closeError : Option Nat)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
    (accepted : filesystemCrashImage chosen masks
      (scan (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position .nil true) = some image)
    (trace : RecordRetry.CrashRetries (Record.low value) (Record.high value)
      (Record.low (~~~value)) (Record.high (~~~value)) image.highWater last) :
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation (reads error (closing closeError) position)) =
      (.ok (.Err ⟨error⟩),scan (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position .nil true) ∧
    restartFilesystem image openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last 4 .nil true) := by
  have afterCrash : filesystemCrashImage chosen masks
      (RecordRetry.phaseEnv (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation .finished) = some image := by
    rw [closed_crash_eq _ _ _ _ generation valid position chosen masks] at accepted
    exact accepted
  have same := RecordRetry.phase_crash _ _ _ _ generation valid .finished chosen masks image afterCrash
  have fresh : 1 ≤ image.highWater := by rw [same]; change 1 ≤ generation + 1; omega
  refine ⟨recover_error _ _ _ _ generation valid position error inside closeError,?_,
    (RecordRetry.finite_retries value image.highWater last trace fresh).2.2⟩
  rw [same]
  exact RecordRecovery.restart_image _ _ _ _ (generation + 1) (by omega)

omit validGeneration in
/-- A failed recovery has a concrete admitted crash, independently of any
assumed admission or Rust contract. -/
theorem error_crash_witness (value : U16) (generation : Nat) (valid : 1 ≤ generation)
    (position error : Nat) (inside : position < 4) (closeError : Option Nat) :
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation (reads error (closing closeError) position)) =
      (.ok (.Err ⟨error⟩),scan (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position .nil true) ∧
    filesystemCrashImage Publish.names [(1,⟨#[0,0,0,0]⟩)]
      (scan (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position .nil true) =
      some ⟨Publish.names,[(1,Record.content value)],generation + 1⟩ := by
  refine ⟨recover_error _ _ _ _ generation valid position error inside closeError,?_⟩
  rw [closed_crash_eq _ _ _ _ generation valid position,content_layout]
  exact RecordRetry.phase_witness _ _ _ _ generation valid .finished

/-- Finite attempts may mix crashes during ready recovery with completed failed
read attempts followed by crashes. Infinite failures carry no success guarantee. -/
inductive Attempts (value : U16) : Nat → Nat → Prop where
  | done (generation : Nat) : Attempts value generation generation
  | interrupted (generation : Nat) (phase : RecordRetry.Phase) (chosen : Names)
      (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
      (accepted : filesystemCrashImage chosen masks
        (RecordRetry.phaseEnv (Record.low value) (Record.high value) (Record.low (~~~value))
          (Record.high (~~~value)) generation phase) = some image)
      (rest : Attempts value image.highWater last) : Attempts value generation last
  | failed (generation position error : Nat) (inside : position < 4) (closeError : Option Nat)
      (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
      (accepted : filesystemCrashImage chosen masks
        (scan (Record.low value) (Record.high value) (Record.low (~~~value))
          (Record.high (~~~value)) generation position .nil true) = some image)
      (rest : Attempts value image.highWater last) : Attempts value generation last

omit validGeneration in
/-- Failure and interruption attempts both preserve acknowledged bytes and fresh
identities. The final ordinary recovery is the actual extracted checked reader. -/
theorem finite_attempts (value : U16) (generation last : Nat) (trace : Attempts value generation last) :
    1 ≤ generation → 1 ≤ last ∧ generation ≤ last ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last 4 .nil true) := by
  induction trace with
  | done generation =>
    intro valid
    exact ⟨valid,Nat.le_refl _,RecordRecovery.recover_value value generation valid⟩
  | interrupted generation phase chosen masks image last accepted rest ih =>
    intro valid
    have same := RecordRetry.phase_crash _ _ _ _ generation valid phase chosen masks image accepted
    have fresh : 1 ≤ image.highWater ∧ generation ≤ image.highWater := by
      rw [same]
      exact RecordRetry.phase_water_valid generation valid phase
    rcases ih fresh.1 with ⟨validLast,ordered,recovered⟩
    exact ⟨validLast,Nat.le_trans fresh.2 ordered,recovered⟩
  | failed generation position error inside closeError chosen masks image last accepted rest ih =>
    intro valid
    have admitted : filesystemCrashImage chosen masks
        (RecordRetry.phaseEnv (Record.low value) (Record.high value) (Record.low (~~~value))
          (Record.high (~~~value)) generation .finished) = some image := by
      rw [closed_crash_eq _ _ _ _ generation valid position] at accepted
      exact accepted
    have same := RecordRetry.phase_crash _ _ _ _ generation valid .finished chosen masks image admitted
    have fresh : 1 ≤ image.highWater ∧ generation ≤ image.highWater := by
      rw [same]
      change 1 ≤ generation + 1 ∧ generation ≤ generation + 1
      omega
    rcases ih fresh.1 with ⟨validLast,ordered,recovered⟩
    exact ⟨validLast,Nat.le_trans fresh.2 ordered,recovered⟩

omit validGeneration in
/-- The initial acknowledged image composes with the mixed failure/interruption
trace and actual final recovery. -/
theorem committed_attempts (env : Environment) (value : U16) (chosen : Names)
    (masks : List (Nat × ByteArray)) (image : FilesystemImage) (last : Nat)
    (accepted : filesystemCrashImage chosen masks (Record.done env value) = some image)
    (trace : Attempts value image.highWater last) :
    restartFilesystem image openingScript =
      some (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) image.highWater) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) last 4 .nil true) := by
  have same := RecordRetry.committed_crash env value chosen masks image accepted
  have valid : 1 ≤ image.highWater := by rw [same]; change 1 ≤ 9; decide +kernel
  refine ⟨?_,(finite_attempts value image.highWater last trace valid).2.2⟩
  rw [same,content_layout]
  exact RecordRecovery.restart_image _ _ _ _ 9 (by decide +kernel)

omit validGeneration in
/-- A nonempty failed attempt is executable and admits its crash; following it
with actual successful recovery needs no assumed first-party contract. -/
theorem one_failed_attempt (value : U16) (generation : Nat) (valid : 1 ≤ generation)
    (position error : Nat) (inside : position < 4) (closeError : Option Nat) :
    recover_file_record (toStr "resource")
      (boot (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation (reads error (closing closeError) position)) =
      (.ok (.Err ⟨error⟩),scan (Record.low value) (Record.high value) (Record.low (~~~value))
        (Record.high (~~~value)) generation position .nil true) ∧
    Attempts value generation (generation + 1) ∧
    recover_file_record (toStr "resource")
      (RecordRecovery.boot (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) (generation + 1)) =
      (.ok (.Ok (some value)),scan (Record.low value) (Record.high value)
        (Record.low (~~~value)) (Record.high (~~~value)) (generation + 1) 4 .nil true) := by
  have executed := error_crash_witness value generation valid position error inside closeError
  have trace : Attempts value generation (generation + 1) :=
    .failed generation position error inside closeError Publish.names [(1,⟨#[0,0,0,0]⟩)]
      ⟨Publish.names,[(1,Record.content value)],generation + 1⟩ _ executed.2 (.done _)
  exact ⟨executed.1,trace,(finite_attempts value generation _ trace valid).2.2⟩

end FileResource.RecordErrors
