module
public import Record.LogProperties
public import Record.ConstructorLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.SharedReadProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties Record.LogProperties

/-- A concrete representation of file state. Both fields must be proved from
actual file-model operations when constructing a view; neither is an axiom. -/
structure FileView (file : NativeFile) where
  environment : State → Environment
  lookup : ∀ state, Valid state → NativeFile.lookup file (environment state) = some state
  store : ∀ before after, Valid before →
    NativeFile.store file after (environment before) = environment after

theorem read_next (file : NativeFile) (view : FileView file)
    (buffer : Slice U8) (before after : State)
    (reply : core.result.Result Usize NativeIoError) (updated : Slice U8)
    (valid : Valid before) (notBlocked : blocked before = false)
    (step : readStep before buffer = some (reply, after, updated))
    (next : core.result.Result Usize NativeIoError × NativeFile × Slice U8 → NativeM α) :
    (io_core.read_once file buffer >>= next).run (view.environment before) =
      (next (reply, file, updated)).run (view.environment after) := by
  have ready : pollRead file buffer (view.environment before) =
      some (.ok (reply, file, updated), view.environment after) := by
    simp [pollRead, view.lookup before valid, notBlocked, step, view.store before after valid]
  simp only [io_core.read_once, monadLift_self, NativeFile.read, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ ready]
  simp [Result.ok_bind]

theorem word_next (file : NativeFile) (view : FileView file)
    (before middle after : State) (lo hi : U8)
    (valid : Valid before) (validMiddle : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one lo))
    (second : readStep middle (one 0#u8) = some (.Ok 1#usize, after, one hi))
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_word file >>= next).run (view.environment before) =
      (next (.Ok (some (word lo hi)), file)).run (view.environment after) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    bind_assoc, Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _).run _ = _
  rw [read_next file view (one 0#u8) before middle _ (one lo) valid notBlocked first]
  simp only [UScalar.ofNatCore_val_eq, bind_assoc]
  change (io_core.read_once file (one 0#u8) >>= _).run _ = _
  rw [read_next file view (one 0#u8) middle after _ (one hi) validMiddle notBlockedMiddle second]
  simp [NativeM.ok, Array.from_slice, one, Array.index_usize,
    NativeM.monadLift_eq, NativeM.fromRust, word, Result.ok_bind]

theorem record_step_next (file : NativeFile) (view : FileView file)
    (before after : State) (value : U16) (step : RecordStep before after value)
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_record file >>= next).run (view.environment before) =
      (next (.Ok (some value), file)).run (view.environment after) := by
  obtain ⟨s1, s2, s3, v0, v1, v2, v3, n0, n1, n2, n3, r0, r1, r2, r3⟩ := step
  simp only [read_record, monadLift_self, bind_assoc]
  rw [word_next file view before s1 s2 _ _ v0 v1 n0 n1 r0 r1]
  simp only [bind_assoc]
  rw [word_next file view s2 s3 after _ _ v2 v3 n2 n3 r2 r3]
  simp [decode_layout, NativeM.ok]

theorem seek_next (file : NativeFile) (view : FileView file) (before after : State)
    (valid : Valid before) (ready : blocked before = false)
    (step : seekStep before (.start 0#u64) = some (.Ok 0#u64, after))
    (next : core.result.Result U64 NativeIoError × NativeFile → NativeM α) :
    (io_core.seek_to file 0#u64 >>= next).run (view.environment before) =
      (next (.Ok 0#u64, file)).run (view.environment after) := by
  have poll : pollSeek file (.start 0#u64) (view.environment before) =
      some (.ok (.Ok 0#u64, file), view.environment after) := by
    simp [pollSeek, view.lookup before valid, ready, step, view.store before after valid]
  simp only [io_core.seek_to, io_core.seek_from, Record.Extraction.FileModel.seek,
    monadLift_self, NativeFile.seek, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp [Result.ok_bind]

theorem loop_records (file : NativeFile) (view : FileView file) (before after : State)
    (values : List U16) (trace : Records before values after)
    (accumulated : List U16) (maxRecords : Usize) (fuel : Nat)
    (count : maxRecords.val = accumulated.length + values.length)
    (capacity : maxRecords.val ≤ 262144) (enough : values.length < fuel)
    (accumulatedValid : accumulated.length ≤ Usize.max) :
    NativeM.loopFuel (fun (file, values) => recover_log_loop.body maxRecords file values)
      fuel (file, alloc.vec.Vec.from accumulated accumulatedValid) (view.environment before) =
      (.ok (.Ok (alloc.vec.Vec.from (accumulated ++ values) (by simp; scalar_tac)), file),
        view.environment after) := by
  induction trace generalizing accumulated fuel with
  | nil state =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have stop : ¬(alloc.vec.Vec.from accumulated accumulatedValid).len < maxRecords := by
        simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv]
        simp only [Usize.ofNatCore, UScalar.ofNatCore_val_eq]
        simp only [List.length_nil, Nat.add_zero] at count
        omega
      simp only [NativeM.loopFuel, recover_log_loop.body, monadLift_self, stop, ite_false,
        NativeM.ok, Result.ok_bind, Result.ok_apply, List.append_nil]
  | @cons before middle value values after step tail ih =>
    cases fuel with
    | zero => simp at enough
    | succ fuel =>
      have go : (alloc.vec.Vec.from accumulated accumulatedValid).len < maxRecords := by
        simp only [alloc.vec.Vec.len, alloc.vec.Vec.from_val, UScalar.lt_equiv]
        simp only [Usize.ofNatCore, UScalar.ofNatCore_val_eq]
        simp only [List.length_cons] at count
        omega
      rw [NativeM.loopFuel]
      simp only [recover_log_loop.body, monadLift_self, go, ite_true, bind_assoc]
      change (read_record file >>= _).run _ = _
      rw [record_step_next file view before middle value step]
      simp only [NativeM.ok]
      rw [push_from accumulated value (by simp only [List.length_cons] at count; omega)]
      simp only [NativeM.monadLift_eq, NativeM.fromRust_ok, Result.ok_bind]
      have recursion := ih (accumulated ++ [value]) fuel
        (by simp only [List.length_append, List.length_cons, List.length_nil] at *; omega)
        (by simp only [List.length_cons] at enough; omega)
        (by simp; scalar_tac)
      simpa only [List.append_assoc, List.cons_append, List.nil_append, recover_log_loop.body, monadLift_self, NativeM.ok, NativeM.monadLift_eq] using recursion

/-- Recovery of any number of records within the declared capacity, grounded
in actual read operations after the actual cross-crate seek. -/
theorem recover_log_records (file : NativeFile) (view : FileView file) (before reset after : State)
    (values : List U16) (maxRecords : Usize)
    (valid : Valid before)
    (ready : blocked before = false)
    (seek : seekStep before (.start 0#u64) = some (.Ok 0#u64, reset))
    (trace : Records reset values after)
    (count : maxRecords.val = values.length) (capacity : values.length ≤ 262144) :
    recover_log file maxRecords (view.environment before) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        view.environment after) := by
  simp only [recover_log, monadLift_self]
  rw [seek_next file view before reset valid ready seek]
  simp only [recover_log_loop, monadLift_self, NativeM.loop]
  have result := loop_records file view reset after values trace [] maxRecords 262145 (by simpa using count) (by omega) (by omega) (by simp)
  simpa only [alloc.vec.Vec.new, List.nil_append] using result


/-- The fresh read-only descriptor produced by reopening inode 1 after restart.
Namespace cells survive every parser read and seek. Old resource owners and
locks are intentionally absent from the restarted machine. -/
@[expose] def reopened (highWater : Nat) (names : Names) (state : State) : Environment := {
  nativeRefCounter := highWater + 1
  nativeHeap := [
    (highWater + 1, handleTypeName, encodeHandle ⟨1,state.position,state.script⟩),
    (0, namespaceTypeName, encodeNamespace ⟨names,names,[],.nil⟩),
    (1, inodeTypeName, encode {state with position := 0, script := .nil})] }

theorem lookup_reopened (highWater : Nat) (names : Names) (state : State)
    (positive : 1 ≤ highWater) (valid : Valid state) :
    lookup ⟨highWater + 1⟩ (reopened highWater names state) = some state := by
  have live : highWater ≠ 0 := by omega
  have liveEq : (highWater == 0) = false := by simp [live]
  have decoded := Record.Properties.decode_encode {state with position := 0, script := .nil}
    ⟨valid.1, valid.2.1, Nat.zero_le _⟩
  have position := not_lt.mpr valid.2.2
  have nonnegative := not_lt.mpr (Int.natCast_nonneg state.position)
  simp [lookup,sharedLookup,getHandle,reopened,decodeHandle,encodeHandle,inode,
    decoded,liveEq,live,position,nonnegative,
    List.filter,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

theorem store_reopened (highWater : Nat) (names : Names) (before after : State)
    (positive : 1 ≤ highWater) (valid : Valid before) :
    store ⟨highWater + 1⟩ after (reopened highWater names before) =
      reopened highWater names after := by
  have live : highWater ≠ 0 := by omega
  have liveEq : (highWater == 0) = false := by simp [live]
  have position := not_lt.mpr valid.2.2
  have nonnegative := not_lt.mpr (Int.natCast_nonneg before.position)
  simp [store,reopened,decodeHandle,encodeHandle,sharedStore,liveEq,live,position,nonnegative,
    List.filter,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]

/-- All file-view obligations are discharged against the concrete shared inode
and descriptor model; recovery never assumes an uninterpreted file contract. -/
def reopenedView (highWater : Nat) (names : Names) (positive : 1 ≤ highWater) :
    FileView ⟨highWater + 1⟩ :=
  { environment := reopened highWater names
    lookup := fun state valid => lookup_reopened highWater names state positive valid
    store := fun before after valid => store_reopened highWater names before after positive valid }

theorem recover_encoded_view (file : NativeFile) (view : FileView file) (values : List U16) (rest : Term) (position : Nat)
    (bounded : values.length ≤ 262144) (offset : position ≤ limit) :
    recover_log file (Usize.ofNatCore values.length (by scalar_tac))
      (view.environment ⟨disk (logBytes values), disk (logBytes values), position,
        recoveryScript (disk (logBytes values)) rest⟩) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), file),
        view.environment (scanning (disk (logBytes values)) rest (4 * values.length))) := by
  have size : (disk (logBytes values)).size = 4 * values.length := by
    simp [disk, ← ByteArray.size_data]
  apply recover_log_records file view _ (scanning (disk (logBytes values)) rest 0) _ values _
  · simp only [Valid, size]
    exact ⟨by simp only [limit]; omega, Nat.le_refl _, offset⟩
  · simp [blocked, recoveryScript, outcome]
  · simpa [scanning, recoveryScript, sought] using Record.RecoveryProperties.seek_start
      (⟨disk (logBytes values), disk (logBytes values), position,
        recoveryScript (disk (logBytes values)) rest⟩ : State)
      0#u64 (zeroMask (disk (logBytes values))) (disk (logBytes values)) _ (by simp [limit])
      (action_outcome _ _ _ _ _) (persist_zero _)
  · simpa only [List.nil_append, List.append_nil, List.length_nil, Nat.zero_add] using
      scanning_records values [] [] rest (by simp [logBytes_length, limit]; omega)
  · simp [Usize.ofNatCore]
  · exact bounded


/-- Recovery is executed through the actual reopened read-only descriptor and
shared inode; every successful read preserves the persistent namespace. -/
theorem recover_reopened_log (highWater : Nat) (names : Names) (values : List U16)
    (rest : Term) (position : Nat) (positive : 1 ≤ highWater)
    (bounded : values.length ≤ 262144) (offset : position ≤ limit) :
    recover_log ⟨highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (reopened highWater names ⟨disk (logBytes values),disk (logBytes values),position,
        recoveryScript (disk (logBytes values)) rest⟩) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨highWater + 1⟩),
        reopened highWater names (scanning (disk (logBytes values)) rest (4 * values.length))) :=
  recover_encoded_view ⟨highWater + 1⟩ (reopenedView highWater names positive)
    values rest position bounded offset

@[expose] def openingScript (script : Term) : Term :=
  .cons (.tuple #[.atom "open",.bitstring Record.ConstructorLogProperties.fileName 0,
    .atom "ok",.integer 0,script]) .nil

@[expose] def boot (highWater : Nat) (data : ByteArray) (script : Term) : Environment := {
  nativeRefCounter := highWater
  nativeHeap := [
    (0,namespaceTypeName,encodeNamespace ⟨Record.ConstructorLogProperties.names,
      Record.ConstructorLogProperties.names,[],openingScript script⟩),
    (1,inodeTypeName,encode ⟨data,data,0,.nil⟩)] }

theorem restart_named_log (highWater : Nat) (data : ByteArray) (script : Term)
    (positive : 1 ≤ highWater) (bounded : data.size ≤ limit) :
    restartFilesystem ⟨Record.ConstructorLogProperties.names,[(1,data)],highWater⟩
      (openingScript script) = some (boot highWater data script) := by
  have supported : supportedPath (⟨#[106,111,117,114,110,97,108]⟩ : ByteArray) = true := by decide +kernel
  simp [supported,restartFilesystem,boot,Record.ConstructorLogProperties.names,
    namespaceTable,namespaceEntry,encodeNames,
    not_lt.mpr bounded,not_lt.mpr positive,List.eraseDups_cons,
    Record.ConstructorLogProperties.fileName]

theorem open_named_log (highWater : Nat) (data : ByteArray) (script : Term)
    (positive : 1 ≤ highWater) (bounded : data.size ≤ limit) :
    io_core.open_readonly (toStr "journal") (boot highWater data script) =
      (.ok (.Ok ⟨highWater + 1⟩),
        reopened highWater Record.ConstructorLogProperties.names ⟨data,data,0,script⟩) := by
  have live : highWater ≠ 0 := by omega
  have liveEq : (highWater == 0) = false := by simp [live]
  have fits : ¬ 1048576 < data.size := not_lt.mpr bounded
  have supported : supportedPath (⟨#[106,111,117,114,110,97,108]⟩ : ByteArray) = true := by decide +kernel
  have poll : pollOpenReadOnly (toStr "journal") (boot highWater data script) =
      some (.ok (.Ok ⟨highWater + 1⟩),
        reopened highWater Record.ConstructorLogProperties.names ⟨data,data,0,script⟩) := by
    simp [fits,supported,pollOpenReadOnly,Record.ConstructorLogProperties.journal_bytes,
      supportedOpenPath,
      boot,reopened,openingScript,Record.ConstructorLogProperties.names,
      namespaceState,namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
      encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,openChoice,pathChoice,
      inode,decode,encode,limit,replaceNamespaceScript,encodeHandle,namespaceTypeName,
      inodeTypeName,handleTypeName,not_lt.mpr positive,liveEq,List.filter,
      Record.ConstructorLogProperties.fileName]
  simp only [io_core.open_readonly,monadLift_self,openReadOnly]
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp

/-- Compose filesystem restart, the extracted Rust opener and the extracted
cross-crate parser without replacing the shared file by an independent file cell. -/
theorem named_log_restart (highWater : Nat) (values : List U16) (rest : Term)
    (positive : 1 ≤ highWater) (bounded : values.length ≤ 262144) :
    let data := disk (logBytes values)
    let script := recoveryScript data rest
    restartFilesystem ⟨Record.ConstructorLogProperties.names,[(1,data)],highWater⟩
      (openingScript script) = some (boot highWater data script) ∧
    io_core.open_readonly (toStr "journal") (boot highWater data script) =
      (.ok (.Ok ⟨highWater + 1⟩),
        reopened highWater Record.ConstructorLogProperties.names ⟨data,data,0,script⟩) ∧
    recover_log ⟨highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (reopened highWater Record.ConstructorLogProperties.names ⟨data,data,0,script⟩) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨highWater + 1⟩),
        reopened highWater Record.ConstructorLogProperties.names
          (scanning data rest (4 * values.length))) := by
  dsimp only
  have size : (disk (logBytes values)).size ≤ limit := by
    simp only [disk,ByteArray.size,List.size_toArray,List.length_map,logBytes_length,limit]
    omega
  exact ⟨restart_named_log highWater _ _ positive size,
    open_named_log highWater _ _ positive size,
    recover_reopened_log highWater _ values rest 0 positive bounded (by simp [limit])⟩

end Record.SharedReadProperties
