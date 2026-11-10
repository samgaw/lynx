defmodule LynxOwnershipFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law accepted_code,
    expects: LynxOwnershipFixture.Native.checked_code(8) == true,
    proof: ~LEAN"""
    have returned := OwnershipNif.Properties.checked (8#u64) (by decide)
    simp [Aeneas.Std.UScalar.ofNatCore] at returned
    simp [«accepted_code:ensures/0», Elixir.LynxOwnershipFixture.Native.«checked_code/1»,
      Elixir.LynxOwnershipFixture.Native.«checked_code:execution/1», Lynx.Rustler.decodeUnsigned,
      returned, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law destructor_panic,
    expects:
      (try do
         LynxOwnershipFixture.Native.checked_code(7) == :nif_panicked
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    have panicked := OwnershipNif.Properties.checked_panics
    simp [Aeneas.Std.UScalar.ofNatCore] at panicked
    simp [«destructor_panic:ensures/0», Elixir.LynxOwnershipFixture.Native.«checked_code/1»,
      Elixir.LynxOwnershipFixture.Native.«checked_code:execution/1», Lynx.Rustler.decodeUnsigned,
      panicked, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law scalar_has_no_destructor_panic,
    expects: LynxOwnershipFixture.Native.scalar_code(7) == true,
    proof: ~LEAN"""
    have returned := OwnershipNif.Properties.scalar (7#u64)
    simp [Aeneas.Std.UScalar.ofNatCore] at returned
    simp [«scalar_has_no_destructor_panic:ensures/0», Elixir.LynxOwnershipFixture.Native.«scalar_code/1»,
      Elixir.LynxOwnershipFixture.Native.«scalar_code:execution/1», Lynx.Rustler.decodeUnsigned,
      returned, Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law scalar_codes(value),
    requires: is_integer(value) and value >= 0 and value <= 18_446_744_073_709_551_615,
    expects: LynxOwnershipFixture.Native.scalar_code(value) == true,
    proof: ~LEAN"""
    cases value <;> simp [«scalar_codes:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i n
    have lo : 0 ≤ n := requires.1
    have hi : n ≤ 18446744073709551615 := requires.2
    have bounds : 0 ≤ n ∧ n < (2^64 : Int) := by norm_num; omega
    let decoded : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 n.toNat⟩
    have decoding : Lynx.Rustler.decodeUnsigned .U64 64 (.integer n) = .ok decoded := by
      rw [Lynx.Rustler.decodeUnsigned, if_pos bounds]
      rfl
    have returned := OwnershipNif.Properties.scalar decoded
    simp [«scalar_codes:ensures/1», Elixir.LynxOwnershipFixture.Native.«scalar_code/1»,
      Elixir.LynxOwnershipFixture.Native.«scalar_code:execution/1», decoding, returned,
      Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law negative_code,
    expects:
      (try do
         LynxOwnershipFixture.Native.checked_code(-1) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«negative_code:ensures/0», Elixir.LynxOwnershipFixture.Native.«checked_code/1»,
      Lynx.Rustler.decodeUnsigned, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law out_of_range,
    expects:
      (try do
         LynxOwnershipFixture.Native.checked_code(18_446_744_073_709_551_616) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«out_of_range:ensures/0», Elixir.LynxOwnershipFixture.Native.«checked_code/1»,
      Lynx.Rustler.decodeUnsigned, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
