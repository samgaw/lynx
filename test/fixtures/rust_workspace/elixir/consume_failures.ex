defmodule LynxRustFixture.ConsumeFailures do
  @compile :debug_info
  use Lynx.Laws

  # Intentionally false on Rustler 0.39.0 / OTP 29: consumption removes the marker.
  law preserves_marker,
    expects: LynxRustFixture.ConsumeNative.payload_length(<<"LYNX", 0, 255>>) == 6,
    proof: ~LEAN"""
    simp [«preserves_marker:ensures/0», Elixir.LynxRustFixture.ConsumeNative.«payload_length/1»,
      Elixir.LynxRustFixture.ConsumeNative.«payload_length:execution/1»,
      Lynx.Rustler.decodeBinary, Consume.NativeProperties.payload, Lynx.Rustler.execute,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """
end
