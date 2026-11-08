module
public import Publish.IoErrors
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.Commit.Framed
open NativeFile Publish.Properties

theorem create_poll (env : Environment)
    (counter : env.nativeRefCounter = (initial).nativeRefCounter)
    (heap : env.nativeHeap = (initial).nativeHeap) : pollCreateNew source env = some (.ok (.Ok ⟨2⟩), {env with nativeRefCounter := (created).nativeRefCounter, nativeHeap := (created).nativeHeap}) := by
  simp [counter,heap,pollCreateNew,source_bytes,valid_a,initial,createChoice,created,pathChoice,
    namespaceSnapshot,namespaceTable,namespaceHistory,tablesEqual,
    encodeNamespace,encodeNames,oldNames,namespaceTypeName,writableHandleTypeName,inodeTypeName,
    storeNamespace,encodeHandle]

theorem sync_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (written value).nativeRefCounter)
    (heap : env.nativeHeap = (written value).nativeHeap) : pollSync ⟨2⟩ env = some (.ok (.Ok ()), {env with nativeRefCounter := (synced value).nativeRefCounter, nativeHeap := (synced value).nativeHeap}) := by
  simp [counter,heap,pollSync,written,synced,syncScript,
    lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,limit,
    content_size,blocked,syncStep,action,
    store,sharedStore,
    encodeNamespace,encodeNames,oldNames,
    renameScript,opening,dirScript,actionOk,
    typeName,handleTypeName,writableHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem close_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (synced value).nativeRefCounter)
    (heap : env.nativeHeap = (synced value).nativeHeap) : pollClose ⟨2⟩ env = some (.ok (), {env with nativeRefCounter := (closed value).nativeRefCounter, nativeHeap := (closed value).nativeHeap}) := by
  simp [counter,heap,pollClose,synced,closed,
    lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,inode,decode,encode,limit,
    content_size,blocked,closeStep,action,
    stable,sharedStore,retire,
    encodeNamespace,encodeNames,oldNames,
    renameScript,opening,dirScript,actionOk,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem rename_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (closed value).nativeRefCounter)
    (heap : env.nativeHeap = (closed value).nativeHeap) : pollRename source target env = some (.ok (.Ok ()), {env with nativeRefCounter := (renamed value).nativeRefCounter, nativeHeap := (renamed value).nativeHeap}) := by
  simp [counter,heap,pollRename,closed,renamed,
    source_bytes,target_bytes,valid_a,valid_b,
    encodeHandle,inode,decode,encode,limit,
    content_size,
    namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    different,renameScript,opening,dirScript,actionOk,
    renameChoice,renamedNames,storeNamespace,
    closedHandleTypeName,
    inodeTypeName,namespaceTypeName]

theorem open_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (renamed value).nativeRefCounter)
    (heap : env.nativeHeap = (renamed value).nativeHeap) : pollOpenReadOnly (toStr ".") env = some (.ok (.Ok ⟨3⟩), {env with nativeRefCounter := (opened value).nativeRefCounter, nativeHeap := (opened value).nativeHeap}) := by
  simp [counter,heap,pollOpenReadOnly,renamed,opened,
    valid_a,valid_b,
    encodeHandle,encode,
    namespaceSnapshot,namespaceState,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    opening,dirScript,actionOk,
    openChoice,pathChoice,replaceNamespaceScript,
    directory_bytes,supportedOpenPath,
    closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName]

theorem dir_sync_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (opened value).nativeRefCounter)
    (heap : env.nativeHeap = (opened value).nativeHeap) : pollSync ⟨3⟩ env = some (.ok (.Ok ()), {env with nativeRefCounter := (checkpointed value).nativeRefCounter, nativeHeap := (checkpointed value).nativeHeap}) := by
  simp [counter,heap,pollSync,pollDirectorySync,opened,checkpointed,
    valid_a,valid_b,
    lookup,encodeHandle,encode,
    action,
    namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,
    encodeNamespace,encodeNames,tablesEqual,List.eraseDups_cons,oldNames,newNames,
    dirScript,actionOk,
    storeNamespace,
    directoryHandle,storeDirectory,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName]

theorem dir_close_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (checkpointed value).nativeRefCounter)
    (heap : env.nativeHeap = (checkpointed value).nativeHeap) : pollClose ⟨3⟩ env = some (.ok (), {env with nativeRefCounter := (done value).nativeRefCounter, nativeHeap := (done value).nativeHeap}) := by
  simp [counter,heap,pollClose,pollDirectoryClose,checkpointed,done,
    lookup,encodeHandle,encode,
    action,
    encodeNamespace,encodeNames,newNames,
    actionOk,
    directoryHandle,storeDirectory,
    typeName,handleTypeName,writableHandleTypeName,closedHandleTypeName,
    inodeTypeName,namespaceTypeName,directoryTypeName,closedDirectoryTypeName]

theorem write_poll (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = (created).nativeRefCounter)
    (heap : env.nativeHeap = (created).nativeHeap) : pollWrite ⟨2⟩ (wire value) env =
    some (.ok (.Ok 2#usize,⟨2⟩), {env with nativeRefCounter := (written value).nativeRefCounter, nativeHeap := (written value).nativeHeap}) := by
  have found : lookup ⟨2⟩ env = some ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2 syncScript⟩ := by
    simp [counter,heap,lookup,sharedLookup,getHandle,decodeHandle,encodeHandle,created,inode,decode,encode,
      limit,typeName,handleTypeName,writableHandleTypeName,inodeTypeName,namespaceTypeName]
  have writable : getHandle ⟨2⟩ handleTypeName env = none := by
    simp [counter,heap,getHandle,created,handleTypeName,writableHandleTypeName]
  have step : writeStep ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2 syncScript⟩ (wire value) =
      some (.Ok 2#usize,⟨content value,ByteArray.empty,2,syncScript⟩) := by
    simp [writeStep,wire_length,writeChoice,action,limit,overwrite,Payload.persist_empty]
    constructor
    · rfl
    · have length : (bytes (wire value)).data.toList.length = 2 := by
        simpa [content,← ByteArray.size_data] using content_size value
      rw [← length,List.take_length]
      rfl
  have ready : blocked ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 2 syncScript⟩ = false := rfl
  simp only [pollWrite,found,ready,Bool.false_eq_true,↓reduceIte,step,writable]
  simp [counter,heap,store,sharedStore,created,written,encodeHandle,decodeHandle,encode,namespaceTypeName,
    writableHandleTypeName,inodeTypeName,typeName]

/-- The actual cross-crate publication runs without modifying scheduler or process state. -/
theorem commit_shared (pid : PID) (value : U16) :
    Result.SharedSteps pid (commit_word source Publish.Properties.target value)
      (initial.nativeRefCounter,initial.nativeHeap) (.Ok true)
      ((done value).nativeRefCounter,(done value).nativeHeap) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  apply Result.SharedSteps.wait _ _ _ _ ((created).nativeRefCounter, (created).nativeHeap) _ _ (fun env _ counter heap => create_poll env counter heap)
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp only [NativeM.lift,Result.ok_bind]
  simp only [io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := write_poll value
  unfold wire at wrote
  apply Result.SharedSteps.wait _ _ _ _ ((written value).nativeRefCounter, (written value).nativeHeap) _ _ (fun env _ counter heap => wrote env counter heap)
  simp only [Result.ok_bind]
  simp only [show (2#usize).val = 2 from rfl]
  simp only [publish_file,synchronize_then_close,sync_directory,io_core.synchronize,
    io_core.rename_file,io_core.open_readonly,monadLift_self,NativeOwnedDrop.drop,
    syncAll,close,NativeFile.rename,openReadOnly,Result.wait_bind]
  apply Result.SharedSteps.wait _ _ _ _ ((synced value).nativeRefCounter, (synced value).nativeHeap) _ _ (fun env _ counter heap => sync_poll value env counter heap)
  simp only [Result.ok_bind,Result.wait_bind]
  apply Result.SharedSteps.wait _ _ _ _ ((closed value).nativeRefCounter, (closed value).nativeHeap) _ _ (fun env _ counter heap => close_poll value env counter heap)
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  apply Result.SharedSteps.wait _ _ _ _ ((renamed value).nativeRefCounter, (renamed value).nativeHeap) _ _ (fun env _ counter heap => rename_poll value env counter heap)
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.fromRust_ok]
  apply Result.SharedSteps.wait _ _ _ _ ((opened value).nativeRefCounter, (opened value).nativeHeap) _ _ (fun env _ counter heap => open_poll value env counter heap)
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.fromRust_ok]
  apply Result.SharedSteps.wait _ _ _ _ ((checkpointed value).nativeRefCounter, (checkpointed value).nativeHeap) _ _ (fun env _ counter heap => dir_sync_poll value env counter heap)
  simp only [Result.ok_bind]
  apply Result.SharedSteps.wait _ _ _ _ ((done value).nativeRefCounter, (done value).nativeHeap) _ _ (fun env _ counter heap => dir_close_poll value env counter heap)
  simpa [NativeM.ok] using (Result.SharedSteps.done (pid := pid) (core.result.Result.Ok true : core.result.Result Bool NativeIoError) ((done value).nativeRefCounter, (done value).nativeHeap))

/-- The native acknowledgement composes with any actual caller continuation. -/
theorem acknowledged_prefix (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = initial.nativeRefCounter)
    (heap : env.nativeHeap = initial.nativeHeap) :
    Result.ReadyPrefix (commit_ack value) env (.ok true)
      {env with nativeRefCounter := (done value).nativeRefCounter,nativeHeap := (done value).nativeHeap} := by
  simp only [commit_ack,monadLift_self,Publish.IoErrors.source_literal,Publish.IoErrors.target_literal]
  have trace := (commit_shared env.currentPid value).readyPrefix env rfl counter heap
  exact trace.bind _



/-- A rejected creation preserves the caller frame and returns its admitted error. -/
theorem creation_error_poll (env : Environment)
    (counter : env.nativeRefCounter = Publish.IoErrors.rejected.nativeRefCounter)
    (heap : env.nativeHeap = Publish.IoErrors.rejected.nativeHeap) :
    pollCreateNew source env = some (.ok (.Err ⟨1⟩),
      {env with nativeRefCounter := Publish.IoErrors.returned.nativeRefCounter, nativeHeap := Publish.IoErrors.returned.nativeHeap}) := by
  simp [pollCreateNew,source_bytes,valid_a,Publish.IoErrors.rejected,Publish.IoErrors.returned,
    counter,heap,pathChoice,namespaceSnapshot,namespaceTable,namespaceHistory,tablesEqual,
    encodeNamespace,encodeNames,namespaceTypeName,replaceNamespaceScript]

/-- Actual Rust error cleanup is an execution prefix, preserving arbitrary continuations. -/
theorem rejected_prefix (value : U16) (env : Environment)
    (counter : env.nativeRefCounter = Publish.IoErrors.rejected.nativeRefCounter)
    (heap : env.nativeHeap = Publish.IoErrors.rejected.nativeHeap) :
    Result.ReadyPrefix (commit_ack value) env (.ok false)
      {env with nativeHeap := Publish.IoErrors.disposed.nativeHeap} := by
  simp only [commit_ack,Publish.IoErrors.source_literal,Publish.IoErrors.target_literal,
    commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (creation_error_poll env counter heap)
  simp [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from,NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp only [io_core.discard_io_error,NativeOwnedDrop.drop,NativeIoError.dispose,
    Result.consumeNativeCapability,monadLift_self,Result.wait_bind]
  refine Result.ReadyPrefix.wait _ _ (Except.ok ()) _
    {env with nativeRefCounter := Publish.IoErrors.returned.nativeRefCounter, nativeHeap := Publish.IoErrors.disposed.nativeHeap} _ _ ?_ ?_
  · simp [Publish.IoErrors.returned,Publish.IoErrors.disposed,NativeIoError.typeName,namespaceTypeName]
  · simpa [Result.ofExcept,NativeM.ok,Publish.IoErrors.returned,Publish.IoErrors.disposed,
      Publish.IoErrors.rejected,counter] using
      (Result.ReadyPrefix.refl (.ok false : Result Bool)
        {env with nativeHeap := Publish.IoErrors.disposed.nativeHeap})

end Publish.Commit.Framed
