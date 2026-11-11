defmodule LynxRustFixture.ConsumeLaws do
  @compile :debug_info
  use Lynx.Laws

  law payload,
    expects: LynxRustFixture.ConsumeNative.payload_length(<<"LYNX", 0, 255>>) == 2,
    proof: ~LEAN"""
    simp [«payload:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.NativeProperties.payload, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law exact_marker,
    expects: LynxRustFixture.ConsumeNative.payload_length("LYNX") == 0,
    proof: ~LEAN"""
    simp [«exact_marker:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.NativeProperties.exact_marker, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law mismatch,
    expects: LynxRustFixture.ConsumeNative.payload_length("LYNY") == nil,
    proof: ~LEAN"""
    simp [«mismatch:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.NativeProperties.mismatch, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Erlang.erlang.«==/2»]
    """

  law truncated,
    expects: LynxRustFixture.ConsumeNative.payload_length(<<>>) == nil,
    proof: ~LEAN"""
    simp [«truncated:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.NativeProperties.truncated, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Erlang.erlang.«==/2»]
    """

  law rejects_nonbinary,
    expects:
      (try do
         LynxRustFixture.ConsumeNative.payload_length(false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonbinary:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«payload_length/1»,
      Lynx.Rustler.decodeBinary, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law comparator_panics,
    expects:
      (try do
         LynxRustFixture.ConsumeNative.checked_consume()
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [«comparator_panics:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«checked_consume/0»,
      Elixir.LynxRustFixture.ConsumeNative.«checked_consume:execution/0»,
      Consume.NativeProperties.comparator_panic, Lynx.Rustler.execute,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law recognition_order,
    expects: LynxRustFixture.ConsumeNative.checked_recognize() == false,
    proof: ~LEAN"""
    simp [«recognition_order:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«checked_recognize/0»,
      Elixir.LynxRustFixture.ConsumeNative.«checked_recognize:execution/0»,
      Consume.NativeProperties.recognition_order, Lynx.Rustler.execute,
      Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """
end
