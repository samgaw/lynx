defmodule LynxRustFixture.IndexedLaws do
  @compile :debug_info
  use Lynx.Laws

  law window_length,
    expects: LynxRustFixture.IndexedNative.window_length(<<0, 255, 128>>, 1, 3) == 2,
    proof: ~LEAN"""
    have n1 : (⟨BitVec.ofNat 8 1⟩ : Aeneas.Std.U8) = 1#u8 := by decide +kernel
    have n3 : (⟨BitVec.ofNat 8 3⟩ : Aeneas.Std.U8) = 3#u8 := by decide +kernel
    simp [n1, n3, «window_length:ensures/0», Elixir.LynxRustFixture.IndexedNative.«window_length/3»,
      Elixir.LynxRustFixture.IndexedNative.«window_length:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned, Indexed.NativeProperties.success,
      Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law reversed_panics,
    expects:
      (try do
         LynxRustFixture.IndexedNative.window_length(<<0, 255, 128>>, 3, 1)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    have n3 : (⟨BitVec.ofNat 8 3⟩ : Aeneas.Std.U8) = 3#u8 := by decide +kernel
    have n1 : (⟨BitVec.ofNat 8 1⟩ : Aeneas.Std.U8) = 1#u8 := by decide +kernel
    simp [n3, n1, «reversed_panics:ensures/0», Elixir.LynxRustFixture.IndexedNative.«window_length/3»,
      Elixir.LynxRustFixture.IndexedNative.«window_length:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned, Indexed.NativeProperties.reversed,
      Lynx.Rustler.execute, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law truncated_panics,
    expects:
      (try do
         LynxRustFixture.IndexedNative.window_length(<<0, 255, 128>>, 0, 4)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    have n0 : (⟨BitVec.ofNat 8 0⟩ : Aeneas.Std.U8) = 0#u8 := by decide +kernel
    have n4 : (⟨BitVec.ofNat 8 4⟩ : Aeneas.Std.U8) = 4#u8 := by decide +kernel
    simp [n0, n4, «truncated_panics:ensures/0», Elixir.LynxRustFixture.IndexedNative.«window_length/3»,
      Elixir.LynxRustFixture.IndexedNative.«window_length:execution/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned, Indexed.NativeProperties.truncated,
      Lynx.Rustler.execute, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_decoder_overflow,
    expects:
      (try do
         LynxRustFixture.IndexedNative.window_length(<<0, 255, 128>>, 0, 4_294_967_296)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_decoder_overflow:ensures/0», Elixir.LynxRustFixture.IndexedNative.«window_length/3»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
