defmodule LynxResourceUnwindFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law reads_resource,
    expects: LynxResourceUnwindFixture.Native.resource_checked(:erlang.get(:held), true) == false,
    proof: ~LEAN"""
    simp [List.eraseDups_cons, List.filter, Resource.Properties.registry_bind,
      Resource.Properties.registry_prefix, Resource.Properties.catch_get,
      Resource.Properties.catch_registry, Resource.Properties.handle_registry,
      Resource.Properties.pinned_pdict, Lynx.concurrentFrom_eq_run, Lynx.Result.monadGet_eq, Lynx.Result.handle, «reads_resource:ensures/0»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked:execution/2»,
      Erlang.erlang.«get/1», Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Resource.Properties.initial, Resource.Properties.seed,
      Resource.Properties.adapter_continuation, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    rw [Resource.Properties.adapter_continuation]
    all_goals simp [Resource.Properties.seed, Lynx.NativeResourceArc.typeName,
      Lynx.Rustler.encodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law repeated_calls,
    expects:
      LynxResourceUnwindFixture.Native.resource_checked(:erlang.get(:held), true) == false and
        LynxResourceUnwindFixture.Native.resource_checked(:erlang.get(:held), true) == false,
    proof: ~LEAN"""
    simp [List.eraseDups_cons, List.filter, Resource.Properties.registry_bind,
      Resource.Properties.registry_prefix, Resource.Properties.catch_get,
      Resource.Properties.catch_registry, Resource.Properties.handle_registry,
      Resource.Properties.pinned_pdict, Lynx.concurrentFrom_eq_run, Lynx.Result.monadGet_eq, Lynx.Result.handle, «repeated_calls:ensures/0»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked:execution/2»,
      Erlang.erlang.«get/1», Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Resource.Properties.initial, Resource.Properties.seed,
      Resource.Properties.adapter_continuation, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    rw [Resource.Properties.adapter_continuation]
    simp [List.eraseDups_cons, List.filter, Resource.Properties.registry_bind,
      Resource.Properties.registry_prefix, Resource.Properties.catch_get,
      Resource.Properties.catch_registry, Resource.Properties.handle_registry,
      Resource.Properties.pinned_pdict, Lynx.concurrentFrom_eq_run, Lynx.Result.monadGet_eq, Lynx.Result.handle, «repeated_calls:ensures/0»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked:execution/2»,
      Erlang.erlang.«get/1», Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Resource.Properties.initial, Resource.Properties.seed,
      Resource.Properties.adapter_continuation, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    all_goals first | rw [Resource.Properties.adapter_continuation] | skip
    all_goals simp [Resource.Properties.seed, Lynx.NativeResourceArc.typeName,
      Lynx.Rustler.encodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law panic_releases_owners,
    expects:
      (try do
         LynxResourceUnwindFixture.Native.resource_checked(:erlang.get(:held), false)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [List.eraseDups_cons, List.filter, Resource.Properties.registry_bind,
      Resource.Properties.registry_prefix, Resource.Properties.catch_get,
      Resource.Properties.catch_registry, Resource.Properties.handle_registry,
      Resource.Properties.pinned_pdict, Lynx.concurrentFrom_eq_run, Lynx.Result.monadGet_eq, Lynx.Result.handle, «panic_releases_owners:ensures/0»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked/2»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked:execution/2»,
      Erlang.erlang.«get/1», Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Resource.Properties.initial, Resource.Properties.seed,
      Resource.Properties.handler_prefix, Lynx.Exception.classTerm, Lynx.Exception.reason]
    rw [Resource.Properties.handler_prefix]
    all_goals simp [Resource.Properties.seed, Lynx.NativeResourceArc.typeName,
      Lynx.Rustler.encodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_wrong_resource,
    expects:
      (try do
         LynxResourceUnwindFixture.Native.resource_checked(7, true)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [List.eraseDups_cons, List.filter, Resource.Properties.registry_bind,
      Resource.Properties.registry_prefix, Resource.Properties.catch_get,
      Resource.Properties.catch_registry, Resource.Properties.handle_registry,
      Resource.Properties.pinned_pdict, Lynx.concurrentFrom_eq_run, Lynx.Result.monadGet_eq, Lynx.Result.handle, «rejects_wrong_resource:ensures/0»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked/2», Lynx.NativeResourceArc.typeName,
      Lynx.Rustler.withResourceTypes, Resource.Properties.pinnedEnv,
      Lynx.NativeResourceArc.decode_eq, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Resource.Properties.initial, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_later_argument,
    expects:
      (try do
         LynxResourceUnwindFixture.Native.resource_checked(:erlang.get(:held), 7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [List.eraseDups_cons, List.filter, Resource.Properties.registry_bind,
      Resource.Properties.registry_prefix, Resource.Properties.catch_get,
      Resource.Properties.catch_registry, Resource.Properties.handle_registry,
      Resource.Properties.pinned_pdict, Lynx.concurrentFrom_eq_run, Lynx.Result.monadGet_eq, Lynx.Result.handle, «rejects_later_argument:ensures/0»,
      Elixir.LynxResourceUnwindFixture.Native.«resource_checked/2», Lynx.NativeResourceArc.typeName,
      Erlang.erlang.«get/1», Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Resource.Properties.initial, Resource.Properties.seed, Resource.Properties.decode_error_prefix,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    rw [Resource.Properties.decode_error_prefix]
    all_goals simp [Resource.Properties.seed, Lynx.NativeResourceArc.typeName,
      Lynx.Rustler.encodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
