defmodule LynxIoFixture.SharedLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law append_existing(value),
    requires: is_integer(value) and value >= 0 and value < 4_294_967_296,
    expects: LynxIoFixture.Native.log_append(:erlang.get(:log), value) == true,
    proof: ~LEAN"""
    cases value <;> simp [«append_existing:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    simp [Lynx.concurrentFrom_eq_run, «append_existing:ensures/1»,
      Erlang.erlang.«get/1», Lynx.Environment.pdict, Lynx.Result.get_continuation_apply, Lynx.Result.monadGet_eq,
      Lynx.Result.get_bind, Lynx.Result.ok_bind,
      Record.NativeLogProperties.initial, Record.NativeLogProperties.pinned,
      Record.FramedLogProperties.framedEnv,
      Elixir.LynxIoFixture.Native.«log_append/2»,
      Elixir.LynxIoFixture.Native.«log_append:execution/2»,
      Lynx.Rustler.decodeUnsigned, range.1, range.2, Lynx.Result.ofExcept,
      Lynx.Rustler.withResourceTypes, Lynx.Result.set_bind, Lynx.Result.set_continuation_apply,
      Lynx.Result.handle, Erlang.erlang.«==/2»]
    rw [Record.NativeLogProperties.initial_adapter _ _ _ _ _ _ schedule]
    all_goals simp [Record.NativeLogProperties.initial, Record.NativeLogProperties.pinned,
      Record.FramedLogProperties.framedEnv]
    """
end
