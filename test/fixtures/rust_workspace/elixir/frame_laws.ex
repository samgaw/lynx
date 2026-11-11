defmodule LynxRustFixture.FrameLaws do
  @compile :debug_info
  use Lynx.Laws

  law payload,
    expects: LynxRustFixture.ConsumeNative.frame_payload_length(<<"LYNX", 0, 255, "\r\n">>) == 2,
    proof: ~LEAN"""
    simp [«payload:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«frame_payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«frame_payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.FrameProperties.payload, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law empty,
    expects: LynxRustFixture.ConsumeNative.frame_payload_length("LYNX\r\n") == 0,
    proof: ~LEAN"""
    simp [«empty:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«frame_payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«frame_payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.FrameProperties.empty, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law trailing,
    expects: LynxRustFixture.ConsumeNative.frame_payload_length(<<"LYNX\r\n", 0>>) == nil,
    proof: ~LEAN"""
    simp [«trailing:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«frame_payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«frame_payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.FrameProperties.trailing, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law comparator_panics,
    expects:
      (try do
         LynxRustFixture.ConsumeNative.checked_suffix()
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [«comparator_panics:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«checked_suffix/0»,
      Elixir.LynxRustFixture.ConsumeNative.«checked_suffix:execution/0»,
      Consume.FrameProperties.comparator_panic, Lynx.Rustler.execute,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
