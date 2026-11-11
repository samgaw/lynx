defmodule LynxRustFixture.PrefixFailures do
  @compile :debug_info
  use Lynx.Laws

  # Intentionally false on Rustler 0.39.0 / OTP 29: the actual marker is accepted.
  law rejects_marker,
    expects: LynxRustFixture.PrefixNative.wire_prefix("LYNX") == false,
    proof: ~LEAN"""
    simp [«rejects_marker:ensures/0», Elixir.LynxRustFixture.PrefixNative.«wire_prefix/1»,
      Elixir.LynxRustFixture.PrefixNative.«wire_prefix:execution/1»,
      Lynx.Rustler.decodeBinary, Prefix.NativeProperties.marker_exact,
      Lynx.Rustler.execute, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """
end
