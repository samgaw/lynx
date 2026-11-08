module
public import Record.ConstructorLogProperties
public import Record.OverlappingLogProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.ConstructedLogProperties
open NativeFile Record.Properties Record.CrashProperties Record.RollbackProperties
  Record.LockedProperties Record.OverlappingLogProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType
  NativeFile.writableHandleTypeName NativeFile.inodeTypeName NativeFile.namespaceTypeName NativeFile.closedDirectoryTypeName

@[expose] def payload : shared_log.LogResource := Record.ConstructorLogProperties.payload
@[expose] def owners (decoded : Bool) : List (Nat × String × Term) :=
  if decoded then (9,NativeResourceArc.handleType shared_log.LogResource,.nativeReference 5) ::
    (NativeResourceArc.vmCells payload 5 7 8).map fun cell => if cell.1 == 5 then
      (5,NativeResourceArc.typeName shared_log.LogResource,.tuple #[.integer 2,NativeCodec.encode payload]) else cell
  else NativeResourceArc.vmCells payload 5 7 8
@[expose] def free : Term := .tuple #[.atom "unlocked",.atom "unpoisoned",.nativeReference 2]
@[expose] def held (env : Environment) : Term := NativeMutex.lockedContents env.currentPid 10 false (⟨2⟩ : NativeFile)
@[expose] def world (env : Environment) (counter : Nat) (decoded : Bool) (mutex : Term) (state : State) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := owners decoded ++ [
    (4,NativeMutex.typeName NativeFile,mutex),
    (3,closedDirectoryTypeName,.tuple #[.nil]),
    (2,writableHandleTypeName,encodeHandle ⟨1,state.position,state.script⟩),
    (1,inodeTypeName,encode {state with position := 0,script := .nil}),
    (0,namespaceTypeName,encodeNamespace ⟨Record.ConstructorLogProperties.names,
      Record.ConstructorLogProperties.names,[],.nil⟩)]}

/-- Logical file state is reconstructed from the actual inode and writable
capability; it is not stored in a substitute standalone file cell. -/
theorem file_lookup (env : Environment) (counter : Nat) (decoded : Bool) (mutex : Term) (state : State)
    (bound : 2 ≤ counter) (valid : Valid state) :
    NativeFile.lookup ⟨2⟩ (world env counter decoded mutex state) = some state := by
  have node : NativeFile.decode (encode {state with position := 0,script := .nil}) =
      some {state with position := 0,script := .nil} :=
    Record.Properties.decode_encode _ ⟨valid.1,valid.2.1,Nat.zero_le _⟩
  have pos : ¬ limit < state.position := not_lt.mpr valid.2.2
  have positive : ¬ (state.position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  have one : ¬ counter < 1 := by omega
  have two : ¬ counter ≤ 1 := by omega
  cases decoded <;>
    simp [NativeFile.lookup,world,owners,NativeResourceArc.vmCells,sharedLookup,getHandle,decodeHandle,
      inode,encodeHandle,node,typeName,writableHandleTypeName,handleTypeName,pos,positive,bound,one,two]

/-- Writing through the constructor's capability updates the shared inode and
its cursor/script, preserving resource ownership, mutex and namespace cells. -/
theorem file_store (env : Environment) (counter : Nat) (decoded : Bool) (mutex : Term) (before after : State)
    (valid : Valid before) :
    store ⟨2⟩ after (world env counter decoded mutex before) = world env counter decoded mutex after := by
  have pos : ¬ limit < before.position := not_lt.mpr valid.2.2
  have positive : ¬ (before.position : Int) < 0 := not_lt.mpr (Int.natCast_nonneg _)
  cases decoded <;>
    simp [store,world,owners,NativeResourceArc.vmCells,decodeHandle,encodeHandle,sharedStore,
      typeName,writableHandleTypeName,handleTypeName,pos,positive]

@[expose] def decoded (env : Environment) (state : State) := world env 9 true free state
@[expose] def locked (env : Environment) (state : State) := world env 10 true (held env) state
@[expose] def unlocked (env : Environment) (state : State) := world env 10 true free state
@[expose] def returned (env : Environment) (state : State) := world env 10 false free state
@[expose] def guard (env : Environment) : NativeGuard NativeFile := ⟨⟨4⟩,10,env.currentPid,⟨2⟩⟩

theorem lock_poll (env : Environment) (state : State) :
    NativeMutex.pollLock (⟨4⟩ : NativeMutex NativeFile) (decoded env state) =
      some (.ok (.Ok (guard env)),locked env state) := by
  have acquired := NativeMutex.pollLock_unlocked (⟨4⟩ : NativeMutex NativeFile)
    (⟨2⟩ : NativeFile) false (decoded env state)
    (by simp [decoded,world,owners,NativeResourceArc.vmCells,free])
    (by simp [decoded,world,owners,NativeResourceArc.vmCells])
  simpa [decoded,locked,world,owners,NativeResourceArc.vmCells,guard,held] using acquired

theorem release_poll (env : Environment) (state : State) :
    NativeGuard.pollRelease (guard env) (locked env state) = some (.ok (),unlocked env state) := by
  simp [NativeGuard.pollRelease,guard,locked,unlocked,world,owners,NativeResourceArc.vmCells,held,
    NativeMutex.lockedContents,NativeCodec.decode,free]

theorem seek_poll (env : Environment) (before after : State) (position : U64)
    (valid : Valid before) (ready : blocked before = false)
    (step : seekStep before (.end_ 0#i64) = some (.Ok position,after)) :
    pollSeek ⟨2⟩ (.end_ 0#i64) (locked env before) =
      some (.ok (.Ok position,⟨2⟩),locked env after) := by
  unfold pollSeek locked
  rw [file_lookup env 10 true (held env) before (by decide) valid]
  simp only [ready,Bool.false_eq_true,↓reduceIte,step]
  rw [file_store env 10 true (held env) before after valid]

theorem write_poll (env : Environment) (before after : State) (value : U16)
    (valid : Valid before) (ready : blocked before = false)
    (step : writeStep before (Record.CrashProperties.payload value) = some (.Ok 4#usize,after)) :
    pollWrite ⟨2⟩ (Record.CrashProperties.payload value) (locked env before) =
      some (.ok (.Ok 4#usize,⟨2⟩),locked env after) := by
  unfold pollWrite locked
  rw [file_lookup env 10 true (held env) before (by decide) valid]
  simp only [ready,Bool.false_eq_true,↓reduceIte,step]
  simp only [show getHandle (⟨2⟩ : NativeFile) handleTypeName (world env 10 true (held env) before) = none by
    simp [getHandle,world,owners,NativeResourceArc.vmCells,handleTypeName,writableHandleTypeName]]
  congr 2
  exact file_store env 10 true (held env) before after valid

theorem sync_poll (env : Environment) (before after : State)
    (valid : Valid before) (ready : blocked before = false)
    (step : syncStep before = some (.Ok (),after)) :
    pollSync ⟨2⟩ (locked env before) = some (.ok (.Ok ()),locked env after) := by
  unfold pollSync locked
  rw [file_lookup env 10 true (held env) before (by decide) valid]
  simp only [ready,Bool.false_eq_true,↓reduceIte,step]
  rw [file_store env 10 true (held env) before after valid]

/-- Append through the actual constructor's capability and inode, then release
its guard and Rust owner while preserving the VM pin and synchronized bytes. -/
theorem append_prefix (env : Environment) (before sought written committed : State)
    (value : U16) (position : U64)
    (valid0 : Valid before) (valid1 : Valid sought) (valid2 : Valid written)
    (ready0 : blocked before = false) (ready1 : blocked sought = false) (ready2 : blocked written = false)
    (seek : seekStep before (.end_ 0#i64) = some (.Ok position,sought))
    (write : writeStep sought (Record.CrashProperties.payload value) = some (.Ok 4#usize,written))
    (sync : syncStep written = some (.Ok (),committed)) :
    Result.ReadyPrefix (__APPEND__ ⟨5,9⟩ value) (decoded env before) (.ok true) (returned env committed) := by
  rw [caller_contract]
  have read := (NativeResourceArc.deref_live_prefix (⟨5,9⟩ : NativeResourceArc shared_log.LogResource)
    payload 2 (decoded env before) (by decide) (by decide)
    (by simp [decoded,world,owners,NativeResourceArc.vmCells])
    (by simp [decoded,world,owners,NativeResourceArc.vmCells])
    (by simp [decoded,world,owners,NativeResourceArc.vmCells])).bind
      (fun log => do let acquired ← NativeMutex.lock log.file
                     afterGuard ⟨5,9⟩ (recoverGuard acquired) value)
  apply read.trans
  simp only [Result.ok_bind,payload,Record.ConstructorLogProperties.payload,NativeMutex.lock,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok (guard env))) _ (locked env before) _ _ (lock_poll env before) ?_
  simp only [Result.ok_bind,recoverGuard,afterGuard,Record.RollbackProperties.append_contract,
    bind_assoc,NativeFile.seek,Result.wait_bind,guard]
  refine .wait _ _ (.ok (.Ok position,(⟨2⟩ : NativeFile))) _ (locked env sought) _ _
    (seek_poll env before sought position valid0 ready0 seek) ?_
  simp only [Result.ok_bind,NativeFile.write,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok (4#usize : Usize),(⟨2⟩ : NativeFile))) _ (locked env written) _ _
    (write_poll env sought written value valid1 ready1 write) ?_
  simp only [Result.ok_bind,NativeFile.syncAll,Result.wait_bind]
  refine .wait _ _ (.ok (.Ok ())) _ (locked env committed) _ _
    (sync_poll env written committed valid2 ready2 sync) ?_
  simp only [Result.ok_bind,NativeGuard.release,Result.wait_bind]
  refine .wait _ _ (.ok ()) _ (unlocked env committed) _ _ (by simpa only [guard] using release_poll env committed) ?_
  simp only [Result.ok_bind]
  have dropped := (NativeResourceArc.releaseOwned_retained_prefix
    (⟨5,9⟩ : NativeResourceArc shared_log.LogResource) payload (unlocked env committed)
    (by simp [unlocked,world,owners,NativeResourceArc.vmCells])
    (by simp [unlocked,world,owners,NativeResourceArc.vmCells])
    (by simp [unlocked,world,owners,NativeResourceArc.vmCells])).bind (fun _ => NativeM.ok true)
  simpa [NativeOwnedDrop.drop,NativeM.ok,unlocked,returned,world,owners,NativeResourceArc.vmCells,List.filter] using dropped

@[expose] def input : State := appendInput ByteArray.empty 0 .nil
@[expose] def soughtState : State := Record.RecoveryProperties.sought input 0 ByteArray.empty
  (Record.Properties.outcome "write" true 4 ByteArray.empty
    (Record.Properties.outcome "sync_all" true 0 ByteArray.empty .nil))
@[expose] def writtenState : State := Record.Properties.written soughtState (Record.CrashProperties.payload 13#u16)
  4 ByteArray.empty (Record.Properties.outcome "sync_all" true 0 ByteArray.empty .nil)
@[expose] def committed : State := Record.AppendProperties.appended input 13#u16 .nil
@[expose] def initial : Environment := Record.ConstructorLogProperties.initial {} input.script

/-- Decode the VM term produced by the constructor, rather than assuming a
separate manually initialized resource exists. -/
theorem decoded_prefix (env : Environment) (script : Term)
    (registered : NativeResourceArc.typeName shared_log.LogResource ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.nativeReference 8))
      (Record.ConstructorLogProperties.constructed env script) (.ok (⟨5,9⟩ : NativeResourceArc shared_log.LogResource))
      (decoded env ⟨ByteArray.empty,ByteArray.empty,0,script⟩) := by
  have head := NativeResourceArc.decode_pinned_prefix Record.ConstructorLogProperties.payload
    (Record.ConstructorLogProperties.constructed env script) 5 7 8
    (Record.ConstructorLogProperties.pinned env script) registered
  simpa [Record.ConstructorLogProperties.constructed,Record.ConstructorLogProperties.mutexReady,
    Record.ConstructorLogProperties.directory,Record.ConstructorLogProperties.fileCells,
    decoded,world,owners,NativeResourceArc.vmCells,payload,free] using head

/-- A closed append witness discharges the file-model premises on the actual
constructed inode/capability; no arbitrary IO success hypotheses remain. -/
theorem appended (env : Environment) :
    Result.ReadyPrefix (__APPEND__ ⟨5,9⟩ 13#u16) (decoded env input) (.ok true) (returned env committed) := by
  apply append_prefix env input soughtState writtenState committed 13#u16 0#u64
  · simp [Valid,input,appendInput,limit]
  · simp [Valid,soughtState,Record.RecoveryProperties.sought,input,appendInput,limit]
  · unfold Valid writtenState Record.Properties.written soughtState Record.RecoveryProperties.sought input appendInput
    decide +kernel
  all_goals rfl

end Record.ConstructedLogProperties
