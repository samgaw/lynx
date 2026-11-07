defmodule LynxIoFixture.ErrorLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_creation(value),
    requires: is_integer(value) and value >= 0 and value < 65536,
    expects: LynxIoFixture.Native.commit(value) == false,
    proof: ~LEAN"""
    cases value <;> simp [«rejected_creation:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    simp [Lynx.concurrentFrom_eq_run, «rejected_creation:ensures/1»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, range.1, range.2, Lynx.Result.ofExcept,
      Publish.Native.rejected_adapter_continuation, Erlang.erlang.«==/2»]
    """

  law rejected_creation_is_a_result,
    expects:
      (try do
         LynxIoFixture.Native.commit(513) == false
       catch
         :error, _ -> false
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run, «rejected_creation_is_a_result:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept,
      Publish.Native.rejected_handler_prefix, Erlang.erlang.«==/2»]
    """
end
