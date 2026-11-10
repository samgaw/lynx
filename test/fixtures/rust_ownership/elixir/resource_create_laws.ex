defmodule LynxResourceCreationFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law creates_true,
    expects: LynxResourceCreationFixture.Native.resource_created(true, true) == false,
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «creates_true:ensures/0»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created/2»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Erlang.erlang.«==/2»]
    rw [Created.Properties.adapter_continuation]
    all_goals simp [Lynx.NativeResourceArc.typeName, Lynx.Rustler.encodeBool]
    """

  law creates_false,
    expects: LynxResourceCreationFixture.Native.resource_created(false, true) == true,
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «creates_false:ensures/0»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created/2»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Erlang.erlang.«==/2»]
    rw [Created.Properties.adapter_continuation]
    all_goals simp [Lynx.NativeResourceArc.typeName, Lynx.Rustler.encodeBool]
    """

  law rejects_after_creation,
    expects:
      (try do
         LynxResourceCreationFixture.Native.resource_created(true, false)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «rejects_after_creation:ensures/0»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created/2»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Lynx.Result.handle, Created.Properties.catch_modify]
    rw [Created.Properties.adapter_handled]
    all_goals simp [Lynx.NativeResourceArc.typeName, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_first_argument,
    expects:
      (try do
         LynxResourceCreationFixture.Native.resource_created(7, true)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «rejects_first_argument:ensures/0»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_second_argument,
    expects:
      (try do
         LynxResourceCreationFixture.Native.resource_created(true, 7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «rejects_second_argument:ensures/0»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law repeated_creation,
    expects:
      LynxResourceCreationFixture.Native.resource_created(true, true) == false and
        LynxResourceCreationFixture.Native.resource_created(false, true) == true,
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «repeated_creation:ensures/0»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created/2»,
      Elixir.LynxResourceCreationFixture.Native.«resource_created:execution/2»,
      Lynx.Rustler.withResourceTypes, Lynx.Result.ofExcept, Lynx.Rustler.decodeBool,
      Lynx.NativeResourceArc.typeName, Erlang.erlang.«==/2»]
    rw [Created.Properties.adapter_continuation]
    all_goals simp [Lynx.NativeResourceArc.typeName, Lynx.Rustler.encodeBool,
      List.eraseDups_cons, List.filter]
    all_goals first | rw [Created.Properties.adapter_continuation] | skip
    all_goals simp [Lynx.NativeResourceArc.typeName, Lynx.Rustler.encodeBool]
    """
end
