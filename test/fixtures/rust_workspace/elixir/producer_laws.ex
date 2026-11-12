defmodule LynxRustFixture.ProducerLaws do
  @compile :debug_info
  use Lynx.Laws

  law roundtrip(input),
    requires: is_binary(input) and byte_size(input) <= 65535,
    expects: LynxRustFixture.ProducerNative.binary_roundtrip(input) == true,
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

  law oversize(input),
    requires: is_binary(input) and byte_size(input) > 65535 and byte_size(input) <= 65538,
    expects: LynxRustFixture.ProducerNative.binary_roundtrip(input) == nil,
    proof: ~LEAN"""
    cases input <;> simp [«oversize:requires/1», Erlang.erlang.«is_binary/1»] at requires
    rename_i bytes bits valid
    rcases bits with ⟨bits, bitBound⟩
    cases bits <;> simp_all [«oversize:requires/1», Erlang.erlang.«is_binary/1», Erlang.erlang.«byte_size/1»]
    have lower : 65535 < bytes.size := by omega
    have upper : bytes.size ≤ 65538 := by omega
    simp [«oversize:ensures/1», Elixir.LynxRustFixture.ProducerNative.«binary_roundtrip/1»,
      Elixir.LynxRustFixture.ProducerNative.«binary_roundtrip:execution/1»,
      ProducerNative.NativeProperties.oversize bytes lower upper,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.execute, Lynx.Rustler.encodeOption, Erlang.erlang.«==/2»]
    """

  law rejects_nonbinary,
    expects:
      (try do
         LynxRustFixture.ProducerNative.binary_roundtrip(false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonbinary:ensures/0», Elixir.LynxRustFixture.ProducerNative.«binary_roundtrip/1»,
      Lynx.Rustler.decodeBinary, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
