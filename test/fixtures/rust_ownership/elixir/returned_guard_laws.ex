defmodule LynxReturnedGuardFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law flips_false,
    expects: LynxReturnedGuardFixture.Native.returned_checked(false) == true,
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «flips_false:ensures/0»]
    rw [Elixir.LynxReturnedGuardFixture.Native.«returned_checked/1»]
    simp only [Lynx.Result.ofExcept, Lynx.Rustler.decodeBool, Lynx.Result.ok_bind]
    rw [Elixir.LynxReturnedGuardFixture.Native.«returned_checked:execution/1»]
    rw [Returned.Properties.adapter_next]
    simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law flips_true,
    expects: LynxReturnedGuardFixture.Native.returned_checked(true) == false,
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «flips_true:ensures/0»]
    rw [Elixir.LynxReturnedGuardFixture.Native.«returned_checked/1»]
    simp only [Lynx.Result.ofExcept, Lynx.Rustler.decodeBool, Lynx.Result.ok_bind]
    rw [Elixir.LynxReturnedGuardFixture.Native.«returned_checked:execution/1»]
    rw [Returned.Properties.adapter_next]
    simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law rejects_integer,
    expects:
      (try do
         LynxReturnedGuardFixture.Native.returned_checked(7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «rejects_integer:ensures/0»,
      Elixir.LynxReturnedGuardFixture.Native.«returned_checked/1», Lynx.Result.ofExcept,
      Lynx.Rustler.decodeBool, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
