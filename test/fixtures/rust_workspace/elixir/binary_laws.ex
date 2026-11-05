defmodule LynxRustFixture.BinaryLaws do
  @compile :debug_info
  use Lynx.Laws

  law binary_roundtrip(value),
    requires: is_binary(value),
    expects: LynxRustFixture.BinaryNative.echo_binary(value) == value,
    proof: ~LEAN"""
    cases value <;> simp [«binary_roundtrip:requires/1», Erlang.erlang.«is_binary/1»] at requires
    rename_i bytes bits valid
    rcases bits with ⟨bits, bound⟩
    cases bits <;> simp_all [«binary_roundtrip:requires/1», Erlang.erlang.«is_binary/1»,
      «binary_roundtrip:ensures/1», Elixir.LynxRustFixture.BinaryNative.«echo_binary/1»,
      Elixir.LynxRustFixture.BinaryNative.«echo_binary:execution/1», RustWorkspace.Binary.facade_spec,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.encodeBinary, Erlang.erlang.«==/2»]
    """

  law binary_length(value),
    requires: is_binary(value) and byte_size(value) <= 2_147_483_647,
    expects: LynxRustFixture.BinaryNative.binary_length(value) == byte_size(value),
    proof: ~LEAN"""
    cases value <;> simp [«binary_length:requires/1», Erlang.erlang.«is_binary/1»] at requires
    rename_i bytes bits valid
    rcases bits with ⟨bits, bound⟩
    cases bits <;> simp_all [«binary_length:requires/1», Erlang.erlang.«is_binary/1»,
      Erlang.erlang.«byte_size/1»]
    have unsigned : bytes.size ≤ Aeneas.Std.Usize.max := by
      cases System.Platform.numBits_eq <;> scalar_tac
    have signed : bytes.size ≤ Aeneas.Std.Isize.max.toNat := by
      cases System.Platform.numBits_eq <;> scalar_tac
    obtain ⟨count, computed, size⟩ := RustWorkspace.Binary.length_facade_spec bytes unsigned signed
    simp [«binary_length:ensures/1», Elixir.LynxRustFixture.BinaryNative.«binary_length/1»,
      Elixir.LynxRustFixture.BinaryNative.«binary_length:execution/1», Lynx.Rustler.decodeBinary,
      computed, Lynx.Rustler.encodeUnsigned, size, Erlang.erlang.«byte_size/1», Erlang.erlang.«==/2»]
    """

  law rejects_nonbinary,
    expects:
      (try do
         LynxRustFixture.BinaryNative.echo_binary([1, 2, 3])
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonbinary:ensures/0», Elixir.LynxRustFixture.BinaryNative.«echo_binary/1»,
      Lynx.Rustler.decodeBinary, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_partial_byte,
    expects:
      (try do
         LynxRustFixture.BinaryNative.echo_binary(<<1::size(1)>>)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_partial_byte:ensures/0», Elixir.LynxRustFixture.BinaryNative.«echo_binary/1»,
      Lynx.Rustler.decodeBinary, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
