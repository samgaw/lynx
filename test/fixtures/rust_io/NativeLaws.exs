defmodule LynxIoFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law published,
    expects: LynxIoFixture.Native.commit(513) == true,
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, «published:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept,
      Publish.Native.adapter_continuation, Erlang.erlang.«==/2»]
    """

  law bounded_publication(value),
    requires: is_integer(value) and value >= 0 and value < 65536,
    expects: LynxIoFixture.Native.commit(value) == true,
    proof: ~LEAN"""
    cases value <;> simp [«bounded_publication:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    simp [Lynx.concurrentFrom_eq_run, «bounded_publication:ensures/1»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, range.1, range.2, Lynx.Result.ofExcept,
      Publish.Native.adapter_continuation, Erlang.erlang.«==/2»]
    """

  law negative,
    expects:
      (try do
         LynxIoFixture.Native.commit(-1)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, «negative:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Lynx.Rustler.decodeUnsigned,
      Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law too_large,
    expects:
      (try do
         LynxIoFixture.Native.commit(4_294_967_296)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, «too_large:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Lynx.Rustler.decodeUnsigned,
      Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law wrong_type,
    expects:
      (try do
         LynxIoFixture.Native.commit(false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, «wrong_type:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Lynx.Rustler.decodeUnsigned,
      Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
