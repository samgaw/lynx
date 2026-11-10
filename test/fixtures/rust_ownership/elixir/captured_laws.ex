defmodule LynxCapturedOwnershipFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law preserves_true,
    expects: LynxCapturedOwnershipFixture.Native.captured_value(true, true) == true,
    proof: ~LEAN"""
    simp [«preserves_true:ensures/0», Elixir.LynxCapturedOwnershipFixture.Native.«captured_value/2»,
      Elixir.LynxCapturedOwnershipFixture.Native.«captured_value:execution/2»,
      Captured.Properties.facade, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law preserves_false,
    expects: LynxCapturedOwnershipFixture.Native.captured_value(false, true) == false,
    proof: ~LEAN"""
    simp [«preserves_false:ensures/0», Elixir.LynxCapturedOwnershipFixture.Native.«captured_value/2»,
      Elixir.LynxCapturedOwnershipFixture.Native.«captured_value:execution/2»,
      Captured.Properties.facade, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law panic_after_cleanup,
    expects:
      (try do
         LynxCapturedOwnershipFixture.Native.captured_value(true, false) == :nif_panicked
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [«panic_after_cleanup:ensures/0», Elixir.LynxCapturedOwnershipFixture.Native.«captured_value/2»,
      Elixir.LynxCapturedOwnershipFixture.Native.«captured_value:execution/2»,
      Captured.Properties.facade, Lynx.Rustler.decodeBool, Lynx.Exception.classTerm,
      Lynx.Exception.reason]
    """

  law rejects_first_argument,
    expects:
      (try do
         LynxCapturedOwnershipFixture.Native.captured_value(7, true) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_first_argument:ensures/0», Elixir.LynxCapturedOwnershipFixture.Native.«captured_value/2»,
      Lynx.Rustler.decodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_second_argument,
    expects:
      (try do
         LynxCapturedOwnershipFixture.Native.captured_value(true, 7) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_second_argument:ensures/0», Elixir.LynxCapturedOwnershipFixture.Native.«captured_value/2»,
      Lynx.Rustler.decodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
