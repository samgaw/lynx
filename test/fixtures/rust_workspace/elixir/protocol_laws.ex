defmodule LynxRustFixture.ProtocolLaws do
  @compile :debug_info
  use Lynx.Laws

  law unicode_frame,
    expects: LynxRustFixture.ProtocolNative.parse_frame(<<1, 2, 195, 169>>) == {:ok, 2},
    proof: ~LEAN"""
    simp [«unicode_frame:ensures/0», Elixir.LynxRustFixture.ProtocolNative.«parse_frame/1»,
      Elixir.LynxRustFixture.ProtocolNative.«parse_frame:execution/1»,
      ProtocolNative.Properties.facade_unicode, Lynx.Rustler.decodeBinary,
      Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law short_frame(value),
    requires: is_binary(value) and byte_size(value) < 2,
    expects: LynxRustFixture.ProtocolNative.parse_frame(value) == {:error, 1},
    proof: ~LEAN"""
    cases value <;> simp [«short_frame:requires/1», Erlang.erlang.«is_binary/1»] at requires
    rename_i bytes bits valid
    rcases bits with ⟨bits, bound⟩
    cases bits <;> simp_all [«short_frame:requires/1», Erlang.erlang.«is_binary/1», Erlang.erlang.«byte_size/1»]
    have short : bytes.size < 2 := by omega
    simp [«short_frame:ensures/1», Elixir.LynxRustFixture.ProtocolNative.«parse_frame/1»,
      Elixir.LynxRustFixture.ProtocolNative.«parse_frame:execution/1»,
      ProtocolNative.Properties.facade_short bytes short, Lynx.Rustler.decodeBinary,
      Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law unicode_validation,
    expects: LynxRustFixture.ProtocolNative.utf8_status(<<1, 2, 195, 169>>) == {:ok, 4},
    proof: ~LEAN"""
    simp [«unicode_validation:ensures/0», Elixir.LynxRustFixture.ProtocolNative.«utf8_status/1»,
      Elixir.LynxRustFixture.ProtocolNative.«utf8_status:execution/1»,
      ProtocolNative.Properties.facade_utf8, Lynx.Rustler.decodeBinary,
      Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """
end
