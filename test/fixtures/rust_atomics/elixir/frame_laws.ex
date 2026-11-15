defmodule LynxFrameFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  @network <<1, 1, 0, :binary.copy(<<7>>, 256)::binary, 1, 0, 0>>

  law empty,
    expects: LynxFrameFixture.Native.frame_summary(<<>>) == {0, 0, 0},
    proof: ~LEAN"""
    simp [«empty:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_summary/1»,
      Elixir.LynxFrameFixture.Native.«frame_summary:execution/1»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.summary_empty, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law one_frame,
    expects: LynxFrameFixture.Native.frame_summary(<<1, 0, 2, 128, 255, 1, 0, 0>>) == {2, 5, 3},
    proof: ~LEAN"""
    simp [«one_frame:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_summary/1»,
      Elixir.LynxFrameFixture.Native.«frame_summary:execution/1»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.summary_frame, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law truncated,
    expects: LynxFrameFixture.Native.frame_summary(<<1, 0, 2, 128>>) == {0, 0, 4},
    proof: ~LEAN"""
    simp [«truncated:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_summary/1»,
      Elixir.LynxFrameFixture.Native.«frame_summary:execution/1»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.summary_truncated, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law wrong_version,
    expects: LynxFrameFixture.Native.frame_summary(<<2, 0, 0>>) == {1, 0, 3},
    proof: ~LEAN"""
    simp [«wrong_version:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_summary/1»,
      Elixir.LynxFrameFixture.Native.«frame_summary:execution/1»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.summary_bad_version, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law empty_payload,
    expects: LynxFrameFixture.Native.frame_summary(<<1, 0, 0>>) == {2, 3, 0},
    proof: ~LEAN"""
    simp [«empty_payload:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_summary/1»,
      Elixir.LynxFrameFixture.Native.«frame_summary:execution/1»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.summary_zero, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law network_order,
    expects: LynxFrameFixture.Native.frame_summary(@network) == {2, 259, 3},
    proof: ~LEAN"""
    -- Pooled literal names derive from their value and are stable across translation order.
    set_option cbv.maxSteps 1000000 in
    have packet : lynx_literal_zs3zaszk =
        Lynx.Term.bitstring ⟨#[1,1,0] ++ (Array.replicate 256 7 ++ #[1,0,0])⟩ 0 (by simp) := by
      cbv
    simp [«network_order:ensures/0», packet,
      Elixir.LynxFrameFixture.Native.«frame_summary/1»,
      Elixir.LynxFrameFixture.Native.«frame_summary:execution/1»,
      Lynx.Rustler.decodeBinary, Frames.NifProperties.summary_network,
      Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law split_middle,
    expects: LynxFrameFixture.Native.frame_split(<<0, 128, 255>>, 1) == {1, 2},
    proof: ~LEAN"""
    have decoded : (⟨BitVec.ofNat 16 1⟩ : Aeneas.Std.U16) = 1#u16 := by decide +kernel
    simp [decoded, «split_middle:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_split/2»,
      Elixir.LynxFrameFixture.Native.«frame_split:execution/2»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.split_middle, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law split_empty,
    expects: LynxFrameFixture.Native.frame_split(<<>>, 0) == {0, 0},
    proof: ~LEAN"""
    have decoded : (⟨BitVec.ofNat 16 0⟩ : Aeneas.Std.U16) = 0#u16 := by decide +kernel
    simp [decoded, «split_empty:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_split/2»,
      Elixir.LynxFrameFixture.Native.«frame_split:execution/2»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.split_empty, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law decoder_narrows,
    expects: LynxFrameFixture.Native.frame_split(<<0, 128, 255>>, 65_536) == {0, 3},
    proof: ~LEAN"""
    have decoded : (⟨BitVec.ofNat 16 0⟩ : Aeneas.Std.U16) = 0#u16 := by decide +kernel
    simp [decoded, «decoder_narrows:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_split/2»,
      Elixir.LynxFrameFixture.Native.«frame_split:execution/2»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.split_zero, Lynx.Rustler.execute, Lynx.Rustler.encodeUnsigned,
      Erlang.erlang.«==/2»]
    """

  law split_panics,
    expects:
      (try do
         LynxFrameFixture.Native.frame_split(<<1>>, 2)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    have decoded : (⟨BitVec.ofNat 16 2⟩ : Aeneas.Std.U16) = 2#u16 := by decide +kernel
    simp [decoded, «split_panics:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_split/2»,
      Elixir.LynxFrameFixture.Native.«frame_split:execution/2»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Frames.NifProperties.split_panic, Lynx.Rustler.execute,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law decoder_rejects,
    expects:
      (try do
         LynxFrameFixture.Native.frame_split(<<1>>, 4_294_967_296)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«decoder_rejects:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_split/2»,
      Elixir.LynxFrameFixture.Native.«frame_split:execution/2»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Lynx.Rustler.execute,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_nonbinary,
    expects:
      (try do
         LynxFrameFixture.Native.frame_split(false, 0)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_nonbinary:ensures/0»,
      Elixir.LynxFrameFixture.Native.«frame_split/2»,
      Elixir.LynxFrameFixture.Native.«frame_split:execution/2»,
      Lynx.Rustler.decodeBinary, Lynx.Rustler.decodeUnsigned,
      Lynx.Rustler.execute,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
