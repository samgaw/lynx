defmodule LynxWorkspaceExample.Proofs do
  use ExUnit.Case
  use Lynx.Case

  @moduletag timeout: 300_000

  laws "native boolean roundtrip", native: {Lynx.Rustler, LynxWorkspaceExample.options()} do
    law restores_true,
      expects: LynxWorkspaceExample.Native.restore(true) == true,
      proof: ~LEAN"""
      simp [«restores_true:ensures/0», Elixir.LynxWorkspaceExample.Native.«restore/1»,
        Elixir.LynxWorkspaceExample.Native.«restore:execution/1», WorkspaceExample.Properties.facade_spec,
        Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
      """

    law restores_false,
      expects: LynxWorkspaceExample.Native.restore(false) == false,
      proof: ~LEAN"""
      simp [«restores_false:ensures/0», Elixir.LynxWorkspaceExample.Native.«restore/1»,
        Elixir.LynxWorkspaceExample.Native.«restore:execution/1», WorkspaceExample.Properties.facade_spec,
        Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
      """

    law rejects_non_boolean,
      expects:
        (try do
           LynxWorkspaceExample.Native.restore(0) == :badarg
         catch
           :error, :badarg -> true
         end),
      proof: ~LEAN"""
      simp [«rejects_non_boolean:ensures/0», Elixir.LynxWorkspaceExample.Native.«restore/1»,
        Lynx.Rustler.decodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
      """
  end

  test "the compiled NIF agrees on valid inputs and rejects non-booleans" do
    assert LynxWorkspaceExample.Native.restore(true)
    refute LynxWorkspaceExample.Native.restore(false)
    assert_raise ArgumentError, fn -> LynxWorkspaceExample.Native.restore(0) end
  end
end
