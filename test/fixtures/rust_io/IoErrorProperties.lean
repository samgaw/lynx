module
public import Publish.Commit
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Publish.IoErrors
open NativeIoError

/-- Actual explicit Rust error destruction consumes exactly the admitted identity. -/
theorem explicit_cleanup (error : NativeIoError) (env : Environment)
    (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ env.nativeRefCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "live")]) :
    io_core.discard_io_error error env = (.ok (),
      {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)}) := by
  simp [io_core.discard_io_error,NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability,
    nonzero,not_lt.mpr bounded,stored]

/-- The compiler-generated implicit cleanup has the same consuming behavior. -/
theorem implicit_cleanup (error : NativeIoError) (env : Environment)
    (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ env.nativeRefCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "live")]) :
    io_core.discard_io_error_implicit error env = (.ok (),
      {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)}) := by
  simp [io_core.discard_io_error_implicit,NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability,
    nonzero,not_lt.mpr bounded,stored]

/-- An unadmitted error never acquires a successful destruction proof. -/
theorem missing_cleanup (error : NativeIoError) (env : Environment)
    (missing : env.nativeHeap.filter (fun cell => cell.1 == error.identity) = []) :
    io_core.discard_io_error error env = (.error .exhausted,env) := by
  simp [io_core.discard_io_error,NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability,missing]

/-- A custom-payload marker does not satisfy OS-only error admission. -/
theorem custom_cleanup (error : NativeIoError) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "custom")]) :
    io_core.discard_io_error error env = (.error .exhausted,env) := by
  simp [io_core.discard_io_error,NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability,stored]

/-- Duplicate identities cannot certify unique error ownership. -/
theorem duplicate_cleanup (error : NativeIoError) (env : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "live"),
       (error.identity,NativeIoError.typeName,.atom "live")]) :
    io_core.discard_io_error error env = (.error .exhausted,env) := by
  simp [io_core.discard_io_error,NativeOwnedDrop.drop,NativeIoError.dispose,Result.consumeNativeCapability,stored]

/-- A consumed error identity cannot be consumed a second time. -/
theorem repeated_cleanup (error : NativeIoError) (env : Environment) :
    io_core.discard_io_error error
      {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)} =
      (.error .exhausted,
        {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)}) := by
  apply missing_cleanup
  simp [List.filter_filter]


open Publish.Commit NativeFile
open Publish.Properties (source a source_bytes valid_a)

theorem source_literal : toStr "a" = source := by
  apply Slice.ext
  simp [toStr,source,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse]
  exact ⟨97, by decide +kernel, by decide +kernel⟩

theorem target_literal : toStr "b" = Publish.Properties.target := by
  apply Slice.ext
  simp [toStr,Publish.Properties.target,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse]
  exact ⟨98, by decide +kernel, by decide +kernel⟩

/-- A complete local ready prefix can be composed with the caller's actual continuation. -/
theorem commit_ready (value : U16) :
    Result.ReadyPrefix (commit_word source Publish.Properties.target value) initial (.ok (.Ok true)) (done value) := by
  simp only [commit_word,io_core.create_new_file,monadLift_self,createNew,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ create_poll
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp only [NativeM.lift,Result.ok_bind]
  simp only [io_core.write_once,monadLift_self,write,Result.wait_bind]
  have wrote := write_poll value
  unfold wire at wrote
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ wrote
  simp only [Result.ok_bind]
  simp only [show (2#usize).val = 2 from rfl]
  simp only [publish_file,synchronize_then_close,sync_directory,io_core.synchronize,
    io_core.rename_file,io_core.open_readonly,monadLift_self,NativeOwnedDrop.drop,
    syncAll,close,NativeFile.rename,openReadOnly,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (sync_poll value)
  simp only [Result.ok_bind,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (close_poll value)
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.ok,core.result.Result.Insts.CoreOpsTry.branch,
    NativeM.monadLift_eq,NativeM.fromRust_ok]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (rename_poll value)
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.fromRust_ok]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (open_poll value)
  simp only [bind_assoc,Result.wait_bind,Result.ok_bind,NativeM.fromRust_ok]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (dir_sync_poll value)
  simp only [Result.ok_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ (dir_close_poll value)
  simpa [NativeM.ok] using (Result.ReadyPrefix.refl (.ok (core.result.Result.Ok true : core.result.Result Bool NativeIoError)) (done value))


/-- The actual cross-crate acknowledgement caller preserves publication success. -/
theorem acknowledged (value : U16) :
    commit_ack value initial = (.ok true,done value) := by
  simp only [commit_ack,monadLift_self,source_literal,target_literal]
  change ((commit_word source Publish.Properties.target value) >>= _) initial = _
  rw [Result.ReadyPrefix.apply ((commit_ready value).bind _)]
  simp [NativeM.ok]

@[expose] def rejected : Environment :=
  {nativeRefCounter := 1,nativeHeap := [
    (1,NativeIoError.typeName,.atom "live"),
    (0,namespaceTypeName,encodeNamespace ⟨[],[],[],
      .cons (.tuple #[.atom "create_new",.bitstring a 0,.atom "error",.integer 1,.nil]) .nil⟩)]}
@[expose] def returned : Environment :=
  {nativeRefCounter := 1,nativeHeap := [
    (1,NativeIoError.typeName,.atom "live"),
    (0,namespaceTypeName,encodeNamespace ⟨[],[],[],.nil⟩)]}
@[expose] def disposed : Environment :=
  {nativeRefCounter := 1,nativeHeap := [(0,namespaceTypeName,encodeNamespace ⟨[],[],[],.nil⟩)]}

theorem creation_error : pollCreateNew source rejected = some (.ok (.Err ⟨1⟩),returned) := by
  simp [pollCreateNew,source_bytes,valid_a,rejected,returned,pathChoice,
    namespaceSnapshot,namespaceTable,namespaceHistory,tablesEqual,
    encodeNamespace,encodeNames,namespaceTypeName,replaceNamespaceScript]

/-- The caller consumes its admitted error and returns false without a file or acknowledgement. -/
theorem rejected_ack (value : U16) : commit_ack value rejected = (.ok false,disposed) := by
  simp only [commit_ack,source_literal,target_literal,commit_word,io_core.create_new_file,monadLift_self,
    createNew,Result.wait_bind]
  try dsimp only
  rw [Result.wait_ready_run _ _ _ _ _ creation_error]
  simp only [Result.ok_bind,core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame,NativeM.monadLift_eq,NativeM.fromRust_ok]
  simp [io_core.discard_io_error,NativeOwnedDrop.drop,NativeIoError.dispose,
    Result.consumeNativeCapability,returned,disposed,NativeM.ok,namespaceTypeName,NativeIoError.typeName]

end Publish.IoErrors
