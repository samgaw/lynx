defmodule LynxTryLockFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law flips_false,
    expects: LynxTryLockFixture.Native.try_checked(false) == {false, false, true, true},
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «flips_false:ensures/0»]
    rw [Elixir.LynxTryLockFixture.Native.«try_checked/1»]
    simp only [Lynx.Result.ofExcept, Lynx.Rustler.decodeBool, Lynx.Result.ok_bind]
    rw [Elixir.LynxTryLockFixture.Native.«try_checked:execution/1»]
    have adapter := TryLock.Properties.adapter_next (β := Lynx.Term) false
    unfold TryLock.Properties.encode at adapter
    rw [adapter]
    simp [TryLock.Properties.encode, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law flips_true,
    expects: LynxTryLockFixture.Native.try_checked(true) == {false, true, true, false},
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «flips_true:ensures/0»]
    rw [Elixir.LynxTryLockFixture.Native.«try_checked/1»]
    simp only [Lynx.Result.ofExcept, Lynx.Rustler.decodeBool, Lynx.Result.ok_bind]
    rw [Elixir.LynxTryLockFixture.Native.«try_checked:execution/1»]
    have adapter := TryLock.Properties.adapter_next (β := Lynx.Term) true
    unfold TryLock.Properties.encode at adapter
    rw [adapter]
    simp [TryLock.Properties.encode, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law rejects_integer,
    expects:
      (try do
         LynxTryLockFixture.Native.try_checked(7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «rejects_integer:ensures/0»,
      Elixir.LynxTryLockFixture.Native.«try_checked/1», Lynx.Result.ofExcept,
      Lynx.Rustler.decodeBool, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
