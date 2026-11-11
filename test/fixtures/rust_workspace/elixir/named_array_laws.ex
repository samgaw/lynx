defmodule LynxRustFixture.NamedArrayLaws do
  @compile :debug_info
  use Lynx.Laws

  law wire_marker,
    expects: LynxRustFixture.NamedArrayNative.wire_marker() == 1_280_921_176,
    proof: ~LEAN"""
    simp [«wire_marker:ensures/0», Elixir.LynxRustFixture.NamedArrayNative.«wire_marker/0»,
      Elixir.LynxRustFixture.NamedArrayNative.«wire_marker:execution/0»,
      NamedArrayNif.Properties.facade, Lynx.Rustler.execute,
      Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """
end
