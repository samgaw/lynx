defmodule LynxEffectsFixture.FailedFileCommits do
  @compile :debug_info
  use Lynx.Laws

  law failed_sync_can_retry,
    expects:
      (
        resource = :erlang.get(:resource)

        not LynxFileResourceFixture.Native.file_commit(resource) and
          LynxFileResourceFixture.Native.file_commit(resource)
      ),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«failed_sync_can_retry:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_commit/1»,
      Elixir.LynxFileResourceFixture.Native.«file_commit:execution/1»,
      Lynx.Rustler.withResourceTypes,Erlang.erlang.«get/1»,Lynx.Result.monadGet_eq,
      Lynx.Environment.pdict,Lynx.Environment.setPdict,FileResource.CommitFailure.seed,
      FileResource.CommitFailure.initial]
    let value : Aeneas.Std.U16 := 4660#u16
    have persisted := FileResource.CommitFailure.zero_saved value
    rw [FileResource.CommitFailure.failure_env value ⟨#[0,0,0,0]⟩ ⟨#[0,0,0,0]⟩
      persisted (FileResource.CreatedCalls.syncChoice .nil)]
    all_goals simp [FileResource.CommitFailure.done,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Publish.commit_run_state
      (FileResource.CommitFailure.after value ⟨#[0,0,0,0]⟩ (FileResource.CreatedCalls.syncChoice .nil))
      (FileResource.Record.synced value)
      (FileResource.CommitFailure.after_valid value _ _ persisted _)
      rfl (FileResource.CommitFailure.retry_step value _)]
    all_goals first | rfl |
      simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """
end
