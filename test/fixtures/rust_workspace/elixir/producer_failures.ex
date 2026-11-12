# Deliberately false: every representable binary payload roundtrips on Rustler 0.39 / OTP 29.
defmodule LynxRustFixture.ProducerFailureLaws do
  @compile :debug_info
  use Lynx.Laws

  law roundtrip(input),
    requires: is_binary(input) and byte_size(input) <= 65535,
    expects: LynxRustFixture.ProducerNative.binary_roundtrip(input) == false,
    proof: ~LEAN"""
    cases input <;> simp [«roundtrip:requires/1», Erlang.erlang.«is_binary/1»] at requires
    rename_i bytes bits valid
    rcases bits with ⟨bits, bitBound⟩
    cases bits <;> simp_all [«roundtrip:requires/1», Erlang.erlang.«is_binary/1», Erlang.erlang.«byte_size/1»]
    have bound : bytes.size ≤ 65535 := by omega
    simp [«roundtrip:ensures/1», Elixir.LynxRustFixture.ProducerNative.«binary_roundtrip/1»,
      Elixir.LynxRustFixture.ProducerNative.«binary_roundtrip:execution/1»,
      ProducerNative.NativeProperties.roundtrip bytes bound,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.execute, Lynx.Rustler.encodeOption,
      Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """
end
