defmodule LynxEffectsFixture.FileCalls do
  @compile :debug_info
  use Lynx.Laws

  law release_then_sync,
    expects:
      (
        resource = :erlang.get(:file)

        LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«release_then_sync:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_release/1»,
      Elixir.LynxFileResourceFixture.Native.«file_release:execution/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync:execution/1»,
      Lynx.Rustler.withResourceTypes,Erlang.erlang.«get/1»,
      Lynx.Result.monadGet_eq,Lynx.Environment.pdict,Lynx.Environment.setPdict,
      FileResource.Calls.seed,FileResource.Calls.pinnedEnv,
      Erlang.erlang.«==/2»]
    rw [FileResource.Calls.release_env FileResource.Calls.before]
    all_goals simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Calls.sync_run FileResource.Calls.before FileResource.Calls.once
      FileResource.Calls.before_valid FileResource.Calls.before_ready FileResource.Calls.first_step]
    all_goals simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """

  law sync_release_sync,
    expects:
      (
        resource = :erlang.get(:file)

        LynxFileResourceFixture.Native.file_sync(resource) and
          LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«sync_release_sync:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_release/1»,
      Elixir.LynxFileResourceFixture.Native.«file_release:execution/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync:execution/1»,
      Lynx.Rustler.withResourceTypes,Erlang.erlang.«get/1»,
      Lynx.Result.monadGet_eq,Lynx.Environment.pdict,Lynx.Environment.setPdict,
      FileResource.Calls.seed,FileResource.Calls.pinnedEnv,Erlang.erlang.«==/2»]
    rw [FileResource.Calls.sync_env FileResource.Calls.before FileResource.Calls.once
      FileResource.Calls.before_valid FileResource.Calls.before_ready FileResource.Calls.first_step]
    all_goals simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName,FileResource.Calls.pinnedEnv]
    rw [FileResource.Calls.release_env FileResource.Calls.once]
    all_goals simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Calls.sync_run FileResource.Calls.once FileResource.Calls.twice
      FileResource.Calls.once_valid FileResource.Calls.once_ready FileResource.Calls.second_step]
    all_goals simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """

  law rejects_integer_sync(input),
    requires: is_integer(input),
    expects:
      (try do
         LynxFileResourceFixture.Native.file_sync(input)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    cases input <;> simp_all [«rejects_integer_sync:requires/1», Erlang.erlang.«is_integer/1»]
    simp only [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«rejects_integer_sync:ensures/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync/1»,Lynx.Rustler.withResourceTypes,
      Lynx.Result.tryWith_eq,Lynx.Result.handle_get,Lynx.Result.handle_set,
      Lynx.Result.get_bind,Lynx.Result.set_bind,Lynx.Result.get_continuation_apply,
      Lynx.Result.set_continuation_apply,bind_assoc]
    rw [Lynx.NativeResourceArc.decode_nonreference_handled_next _ (by intro identity; simp)]
    simp [Lynx.Result.ok_bind,Lynx.Result.ok_apply,Lynx.Exception.classTerm,Lynx.Exception.reason]
    """
end
