# Intentionally false on Rustler 0.39.0 / OTP 29: u8 decoding narrows a u32.
# Keep the general safety property; concrete counterexamples are ordinary tests.
defmodule LynxRustFixture.IndexedFailures do
  @compile :debug_info
  use Lynx.Laws

  law rejects_narrowed_endpoints(endpoint),
    requires: is_integer(endpoint) and endpoint > 255,
    expects:
      (try do
         LynxRustFixture.IndexedNative.window_length(<<0, 255, 128>>, 0, endpoint)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    cases endpoint <;> simp_all [«rejects_narrowed_endpoints:requires/1», Erlang.erlang.«is_integer/1»]
    simp [«rejects_narrowed_endpoints:ensures/1», Elixir.LynxRustFixture.IndexedNative.«window_length/3»,
      Elixir.LynxRustFixture.IndexedNative.«window_length:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned, Indexed.NativeProperties.facade,
      Lynx.Rustler.execute, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
