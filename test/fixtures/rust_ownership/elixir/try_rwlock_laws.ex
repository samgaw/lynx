defmodule LynxTryRwFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law flips_false,
    expects: LynxTryRwFixture.Native.try_rw_checked(false) == {false, false, true, true},
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «flips_false:ensures/0»]
    rw [Elixir.LynxTryRwFixture.Native.«try_rw_checked/1»]
    simp only [Lynx.Result.ofExcept, Lynx.Rustler.decodeBool, Lynx.Result.ok_bind]
    rw [Elixir.LynxTryRwFixture.Native.«try_rw_checked:execution/1»]
    have adapter := TryRw.Properties.adapter_next (β := Lynx.Term) false
    unfold TryRw.Properties.encode at adapter
    rw [adapter]
    simp [TryRw.Properties.encode, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law flips_true,
    expects: LynxTryRwFixture.Native.try_rw_checked(true) == {false, false, true, false},
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «flips_true:ensures/0»]
    rw [Elixir.LynxTryRwFixture.Native.«try_rw_checked/1»]
    simp only [Lynx.Result.ofExcept, Lynx.Rustler.decodeBool, Lynx.Result.ok_bind]
    rw [Elixir.LynxTryRwFixture.Native.«try_rw_checked:execution/1»]
    have adapter := TryRw.Properties.adapter_next (β := Lynx.Term) true
    unfold TryRw.Properties.encode at adapter
    rw [adapter]
    simp [TryRw.Properties.encode, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law rejects_integer,
    expects:
      (try do
         LynxTryRwFixture.Native.try_rw_checked(7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «rejects_integer:ensures/0»,
      Elixir.LynxTryRwFixture.Native.«try_rw_checked/1», Lynx.Result.ofExcept,
      Lynx.Rustler.decodeBool, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
