defmodule LynxRustFixture.TextViewsLaws do
  @compile :debug_info
  use Lynx.Laws

  law byte_offset,
    expects: LynxRustFixture.TextNative.text_payload(<<195, 169>>, 1) == {:ok, 1},
    proof: ~LEAN"""
    have one : (⟨BitVec.ofNat 8 1⟩ : Aeneas.Std.U8) = 1#u8 := by decide +kernel
    simp [one, «byte_offset:ensures/0», Elixir.LynxRustFixture.TextNative.«text_payload/2»,
      Elixir.LynxRustFixture.TextNative.«text_payload:execution/2»,
      TextViews.Properties.facade_inside_character, Lynx.Rustler.decodeBinary,
      Lynx.Rustler.decodeUnsigned, Lynx.Rustler.execute, Lynx.Rustler.encodeResult,
      Lynx.Rustler.encodeOption, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law truncated,
    expects: LynxRustFixture.TextNative.text_payload(<<195, 169>>, 3) == {:ok, nil},
    proof: ~LEAN"""
    have three : (⟨BitVec.ofNat 8 3⟩ : Aeneas.Std.U8) = 3#u8 := by decide +kernel
    simp [three, «truncated:ensures/0», Elixir.LynxRustFixture.TextNative.«text_payload/2»,
      Elixir.LynxRustFixture.TextNative.«text_payload:execution/2»,
      TextViews.Properties.facade_truncated, Lynx.Rustler.decodeBinary,
      Lynx.Rustler.decodeUnsigned, Lynx.Rustler.execute, Lynx.Rustler.encodeResult,
      Lynx.Rustler.encodeOption, Erlang.erlang.«==/2»]
    """

  law invalid_text,
    expects: LynxRustFixture.TextNative.text_payload(<<255>>, 0) == {:error, 4},
    proof: ~LEAN"""
    simp [«invalid_text:ensures/0», Elixir.LynxRustFixture.TextNative.«text_payload/2»,
      Elixir.LynxRustFixture.TextNative.«text_payload:execution/2»,
      TextViews.Properties.facade_invalid, Lynx.Rustler.decodeBinary,
      Lynx.Rustler.decodeUnsigned, Lynx.Rustler.execute, Lynx.Rustler.encodeResult,
      Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """
end
