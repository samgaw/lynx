# Deliberately false: the two-child packet contains three nodes on Rustler 0.39 / OTP 29.
defmodule LynxRustFixture.NestedFailureLaws do
  @compile :debug_info
  use Lynx.Laws

  law siblings,
    expects:
      LynxRustFixture.NestedNative.document_nodes(<<1, 0, 8, 0, 0, 0, 2, 0, 2, 195, 169>>, 2, 3) ==
        4,
    proof: ~LEAN"""
    simp [«siblings:ensures/0», Elixir.LynxRustFixture.NestedNative.«document_nodes/3»,
      Elixir.LynxRustFixture.NestedNative.«document_nodes:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      NestedNative.NativeProperties.facade_siblings, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """
end
