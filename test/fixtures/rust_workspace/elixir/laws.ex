defmodule LynxRustFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law restores_true,
    expects: LynxRustFixture.Native.restore(true) == true,
    proof: ~LEAN"""
    simp [«restores_true:ensures/0», Elixir.LynxRustFixture.Native.«restore/1»,
      Elixir.LynxRustFixture.Native.«restore:execution/1», RustWorkspace.Native.facade_spec,
      Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law restores_false,
    expects: LynxRustFixture.Native.restore(false) == false,
    proof: ~LEAN"""
    simp [«restores_false:ensures/0», Elixir.LynxRustFixture.Native.«restore/1»,
      Elixir.LynxRustFixture.Native.«restore:execution/1», RustWorkspace.Native.facade_spec,
      Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law negates_true,
    expects: LynxRustFixture.Native.negate(true) == false,
    proof: ~LEAN"""
    simp [«negates_true:ensures/0», Elixir.LynxRustFixture.Native.«negate/1»,
      Elixir.LynxRustFixture.Native.«negate:execution/1», RustWorkspace.Native.negate_spec,
      Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law calculates_linear(value),
    requires:
      is_integer(value) and value >= -4_611_686_018_427_387_904 and
        value <= 4_611_686_018_427_387_903,
    expects: LynxRustFixture.Native.calculate(value) == value * 2 + 1,
    proof: ~LEAN"""
    cases value <;> simp [«calculates_linear:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i n
    have lo : -4611686018427387904 ≤ n := requires.1
    have hi : n ≤ 4611686018427387903 := requires.2
    have valid : -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) := by norm_num; omega
    let decoded : Aeneas.Std.I64 := Aeneas.Std.I64.ofIntCore n valid
    have decoded_value : decoded.val = n := by simp [decoded]
    have decoding : Lynx.Rustler.decodeSigned .I64 64 (.integer n) = .ok decoded := by
      rw [Lynx.Rustler.decodeSigned, ite_eq_left valid]
      rfl
    obtain ⟨result, result_value, execution⟩ := Lynx.Rustler.execute_of_spec
      (RustWorkspace.Native.integer_facade decoded (by simpa [decoded_value] using lo)
        (by simpa [decoded_value] using hi)) Lynx.Rustler.encodeSigned
    simp [«calculates_linear:ensures/1», Elixir.LynxRustFixture.Native.«calculate/1»,
      Elixir.LynxRustFixture.Native.«calculate:execution/1», decoding, execution,
      Lynx.Rustler.encodeSigned, result_value, decoded_value, Erlang.erlang.«==/2»]
    """

  law rejects_integer_range,
    expects:
      (try do
         LynxRustFixture.Native.calculate(9_223_372_036_854_775_808) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_integer_range:ensures/0», Elixir.LynxRustFixture.Native.«calculate/1»,
      Lynx.Rustler.decodeSigned, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law catches_integer_overflow,
    expects:
      (try do
         LynxRustFixture.Native.calculate(4_611_686_018_427_387_904) == :nif_panicked
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    have panic := RustWorkspace.BridgeTests.overflow_is_panic
    simp [Aeneas.Std.IScalar.ofInt, Aeneas.Std.IScalar.ofIntCore] at panic
    simp [«catches_integer_overflow:ensures/0», Elixir.LynxRustFixture.Native.«calculate/1»,
      Elixir.LynxRustFixture.Native.«calculate:execution/1», Lynx.Rustler.decodeSigned,
      panic, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
