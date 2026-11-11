defmodule LynxRustFixture.NestedLaws do
  @compile :debug_info
  use Lynx.Laws

  law siblings,
    expects:
      LynxRustFixture.NestedNative.document_nodes(<<1, 0, 8, 0, 0, 0, 2, 0, 2, 195, 169>>, 2, 3) ==
        3,
    proof: ~LEAN"""
    simp [«siblings:ensures/0», Elixir.LynxRustFixture.NestedNative.«document_nodes/3»,
      Elixir.LynxRustFixture.NestedNative.«document_nodes:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      NestedNative.NativeProperties.facade_siblings, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law narrowed_budgets,
    expects:
      LynxRustFixture.NestedNative.document_nodes(
        <<1, 0, 8, 0, 0, 0, 2, 0, 2, 195, 169>>,
        258,
        65539
      ) == 3,
    proof: ~LEAN"""
    simp [«narrowed_budgets:ensures/0», Elixir.LynxRustFixture.NestedNative.«document_nodes/3»,
      Elixir.LynxRustFixture.NestedNative.«document_nodes:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      NestedNative.NativeProperties.facade_siblings, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law rejects_depth_range,
    expects:
      (try do
         LynxRustFixture.NestedNative.document_nodes(<<>>, 4_294_967_296, 1)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_depth_range:ensures/0», Elixir.LynxRustFixture.NestedNative.«document_nodes/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_node_range,
    expects:
      (try do
         LynxRustFixture.NestedNative.document_nodes(<<>>, 1, 4_294_967_296)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_node_range:ensures/0», Elixir.LynxRustFixture.NestedNative.«document_nodes/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
