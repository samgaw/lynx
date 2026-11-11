defmodule LynxRustFixture.PrefixLaws do
  @compile :debug_info
  use Lynx.Laws

  law recognizes_marker,
    expects: LynxRustFixture.PrefixNative.wire_prefix("LYNX") == true,
    proof: ~LEAN"""
    simp [«recognizes_marker:ensures/0», Elixir.LynxRustFixture.PrefixNative.«wire_prefix/1»,
      Elixir.LynxRustFixture.PrefixNative.«wire_prefix:execution/1»,
      Lynx.Rustler.decodeBinary, Prefix.NativeProperties.marker_exact,
      Lynx.Rustler.execute, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law preserves_binary_payload,
    expects: LynxRustFixture.PrefixNative.wire_prefix(<<"LYNX", 0, 255, 128>>) == true,
    proof: ~LEAN"""
    simp [«preserves_binary_payload:ensures/0», Elixir.LynxRustFixture.PrefixNative.«wire_prefix/1»,
      Elixir.LynxRustFixture.PrefixNative.«wire_prefix:execution/1»,
      Lynx.Rustler.decodeBinary, Prefix.NativeProperties.marker_payload,
      Lynx.Rustler.execute, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law rejects_short,
    expects: LynxRustFixture.PrefixNative.wire_prefix(<<>>) == false,
    proof: ~LEAN"""
    simp [«rejects_short:ensures/0», Elixir.LynxRustFixture.PrefixNative.«wire_prefix/1»,
      Elixir.LynxRustFixture.PrefixNative.«wire_prefix:execution/1»,
      Lynx.Rustler.decodeBinary, Prefix.NativeProperties.reject_short,
      Lynx.Rustler.execute, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law short_circuits,
    expects: LynxRustFixture.PrefixNative.checked_prefix(false) == false,
    proof: ~LEAN"""
    simp [«short_circuits:ensures/0», Elixir.LynxRustFixture.PrefixNative.«checked_prefix/1»,
      Elixir.LynxRustFixture.PrefixNative.«checked_prefix:execution/1»,
      Lynx.Rustler.decodeBool, Prefix.NativeProperties.short_circuit,
      Lynx.Rustler.execute, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law rejects_nonbinary,
    expects:
      (try do
         LynxRustFixture.PrefixNative.wire_prefix(false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonbinary:ensures/0», Elixir.LynxRustFixture.PrefixNative.«wire_prefix/1»,
      Lynx.Rustler.decodeBinary, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_nonboolean,
    expects:
      (try do
         LynxRustFixture.PrefixNative.checked_prefix(0)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonboolean:ensures/0», Elixir.LynxRustFixture.PrefixNative.«checked_prefix/1»,
      Lynx.Rustler.decodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law comparator_panics,
    expects:
      (try do
         LynxRustFixture.PrefixNative.checked_prefix(true)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    simp [«comparator_panics:ensures/0», Elixir.LynxRustFixture.PrefixNative.«checked_prefix/1»,
      Elixir.LynxRustFixture.PrefixNative.«checked_prefix:execution/1»,
      Lynx.Rustler.decodeBool, Prefix.NativeProperties.comparator_panic,
      Lynx.Rustler.execute, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
