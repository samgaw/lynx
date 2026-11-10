defmodule LynxGuardUnwindFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law preserves_true,
    expects: LynxGuardUnwindFixture.Native.guarded_value(true, true) == true,
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, Lynx.Result.ofExcept, «preserves_true:ensures/0», Elixir.LynxGuardUnwindFixture.Native.«guarded_value/2»,
      Elixir.LynxGuardUnwindFixture.Native.«guarded_value:execution/2»,
      Guard.Properties.adapter_continuation, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law accepts_false,
    expects: LynxGuardUnwindFixture.Native.guarded_value(false, true) == true,
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, Lynx.Result.ofExcept, «accepts_false:ensures/0», Elixir.LynxGuardUnwindFixture.Native.«guarded_value/2»,
      Elixir.LynxGuardUnwindFixture.Native.«guarded_value:execution/2»,
      Guard.Properties.adapter_continuation, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law panic_after_cleanup,
    expects:
      (try do
         LynxGuardUnwindFixture.Native.guarded_value(true, false) == :nif_panicked
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, Lynx.Result.ofExcept, «panic_after_cleanup:ensures/0», Elixir.LynxGuardUnwindFixture.Native.«guarded_value/2»,
      Elixir.LynxGuardUnwindFixture.Native.«guarded_value:execution/2»,
      Guard.Properties.handler_prefix, Lynx.Rustler.decodeBool, Lynx.Exception.classTerm,
      Lynx.Exception.reason]
    """

  law rejects_first_argument,
    expects:
      (try do
         LynxGuardUnwindFixture.Native.guarded_value(7, true) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, Lynx.Result.ofExcept, «rejects_first_argument:ensures/0», Elixir.LynxGuardUnwindFixture.Native.«guarded_value/2»,
      Lynx.Rustler.decodeBool, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_second_argument,
    expects:
      (try do
         LynxGuardUnwindFixture.Native.guarded_value(true, 7) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, Lynx.Result.ofExcept, «rejects_second_argument:ensures/0», Elixir.LynxGuardUnwindFixture.Native.«guarded_value/2»,
      Lynx.Rustler.decodeBool, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
