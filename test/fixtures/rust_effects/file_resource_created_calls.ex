defmodule LynxEffectsFixture.CreatedFileCalls do
  @compile :debug_info
  use Lynx.Laws

  law create_release_sync,
    expects:
      (
        resource = LynxFileResourceFixture.Native.file_create()

        LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«create_release_sync:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create:execution/0»,
      Elixir.LynxFileResourceFixture.Native.«file_release/1»,
      Elixir.LynxFileResourceFixture.Native.«file_release:execution/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync:execution/1»,
      Lynx.Rustler.withResourceTypes,Erlang.erlang.«==/2»]
    rw [FileResource.Creation.create_env (rest := .nil) FileResource.CreatedCalls.before.script]
    all_goals simp [FileResource.CreatedCalls.seed,FileResource.Creation.initial,
      FileResource.CreatedCalls.returned_before,FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.CreatedCalls.release_env (ns := FileResource.CreatedCalls.pendingNamespace) FileResource.CreatedCalls.before]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.CreatedCalls.sync_run (ns := FileResource.CreatedCalls.pendingNamespace) FileResource.CreatedCalls.before FileResource.CreatedCalls.once
      FileResource.CreatedCalls.before_valid FileResource.CreatedCalls.before_ready FileResource.CreatedCalls.first_step]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """

  law create_sync_release_sync,
    expects:
      (
        resource = LynxFileResourceFixture.Native.file_create()

        LynxFileResourceFixture.Native.file_sync(resource) and
          LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«create_sync_release_sync:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create:execution/0»,
      Elixir.LynxFileResourceFixture.Native.«file_release/1»,
      Elixir.LynxFileResourceFixture.Native.«file_release:execution/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync:execution/1»,
      Lynx.Rustler.withResourceTypes,Erlang.erlang.«==/2»]
    rw [FileResource.Creation.create_env (rest := .nil) FileResource.CreatedCalls.before.script]
    all_goals simp [FileResource.CreatedCalls.seed,FileResource.Creation.initial,
      FileResource.CreatedCalls.returned_before,FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.CreatedCalls.sync_env (ns := FileResource.CreatedCalls.pendingNamespace) FileResource.CreatedCalls.before FileResource.CreatedCalls.once
      FileResource.CreatedCalls.before_valid FileResource.CreatedCalls.before_ready FileResource.CreatedCalls.first_step]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.CreatedCalls.release_env (ns := FileResource.CreatedCalls.pendingNamespace) FileResource.CreatedCalls.once]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.CreatedCalls.sync_run (ns := FileResource.CreatedCalls.pendingNamespace) FileResource.CreatedCalls.once FileResource.CreatedCalls.twice
      FileResource.CreatedCalls.once_valid FileResource.CreatedCalls.once_ready FileResource.CreatedCalls.second_step]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """
end
