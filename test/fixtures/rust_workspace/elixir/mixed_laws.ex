defmodule LynxRustFixture.MixedLaws do
  @compile :debug_info
  use Lynx.Laws

  law local_helper,
    expects: LynxRustFixture.Native.restored(true) == true,
    proof: ~LEAN"""
    simp [«local_helper:ensures/0», Elixir.LynxRustFixture.Native.«restored/1»,
      Elixir.LynxRustFixture.Native.«restore/1»,
      Elixir.LynxRustFixture.Native.«restore:execution/1», RustWorkspace.Native.facade_spec,
      Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law remote_helper,
    expects: LynxRustFixture.Native.restored_remotely(false) == false,
    proof: ~LEAN"""
    simp [«remote_helper:ensures/0», Elixir.LynxRustFixture.Native.«restored_remotely/1»,
      Elixir.LynxRustFixture.Native.«restore/1»,
      Elixir.LynxRustFixture.Native.«restore:execution/1», RustWorkspace.Native.facade_spec,
      Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law captured_helper,
    expects: LynxRustFixture.Native.restored_by_fun(true) == true,
    proof: ~LEAN"""
    simp [Lynx.apply, «captured_helper:ensures/0»,
      Elixir.LynxRustFixture.Native.«restored_by_fun/1»,
      Elixir.LynxRustFixture.Native.«restore_fun/0»,
      Elixir.LynxRustFixture.Native.«restore/1»,
      Elixir.LynxRustFixture.Native.«restore:execution/1», RustWorkspace.Native.facade_spec,
      Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """
end
