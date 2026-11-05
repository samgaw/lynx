defmodule LynxRustFixture.CompositeLaws do
  @compile :debug_info
  use Lynx.Laws

  law transforms_tuple,
    expects: LynxRustFixture.CompositeNative.transform_pair({true, 42}) == {false, 42},
    proof: ~LEAN"""
    simp [«transforms_tuple:ensures/0», Elixir.LynxRustFixture.CompositeNative.«transform_pair/1»,
      Elixir.LynxRustFixture.CompositeNative.«transform_pair:execution/1»,
      RustWorkspace.Composite.tuple_facade, Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField,
      Lynx.Rustler.decodeBool, Lynx.Rustler.decodeSigned, Lynx.Rustler.encodeBool,
      Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;> norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
    """

  law classifies_integer(value),
    requires:
      is_integer(value) and value >= -9_223_372_036_854_775_808 and
        value <= 9_223_372_036_854_775_807,
    expects: LynxRustFixture.CompositeNative.classify({true, value}) == {:ok, value},
    proof: ~LEAN"""
    cases value <;> simp [«classifies_integer:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i n
    have valid : -(2^63 : Int) ≤ n ∧ n < (2^63 : Int) := by norm_num; omega
    let decoded : Aeneas.Std.I64 := Aeneas.Std.I64.ofIntCore n valid
    have decoded_value : decoded.val = n := by simp [decoded]
    have decoding : Lynx.Rustler.decodeSigned .I64 64 (.integer n) = .ok decoded := by
      rw [Lynx.Rustler.decodeSigned, ite_eq_left valid]
      rfl
    simp [«classifies_integer:ensures/1», Elixir.LynxRustFixture.CompositeNative.«classify/1»,
      Elixir.LynxRustFixture.CompositeNative.«classify:execution/1»,
      Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeBool, decoding,
      RustWorkspace.Composite.classify_facade, Lynx.Rustler.encodeResult,
      Lynx.Rustler.encodeSigned, decoded_value, Erlang.erlang.«==/2»]
    """

  law rejection_is_a_value,
    expects: LynxRustFixture.CompositeNative.classify({false, 42}) == {:error, 7},
    proof: ~LEAN"""
    simp [«rejection_is_a_value:ensures/0», Elixir.LynxRustFixture.CompositeNative.«classify/1»,
      Elixir.LynxRustFixture.CompositeNative.«classify:execution/1»,
      Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeBool,
      Lynx.Rustler.decodeSigned, RustWorkspace.Composite.classify_facade,
      Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law ordinary_result_error,
    expects: LynxRustFixture.CompositeNative.reverse_result({:ok, 5}) == {:error, 5},
    proof: ~LEAN"""
    simp [«ordinary_result_error:ensures/0», Elixir.LynxRustFixture.CompositeNative.«reverse_result/1»,
      Elixir.LynxRustFixture.CompositeNative.«reverse_result:execution/1»,
      Lynx.Rustler.decodeResult, Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField,
      Lynx.Rustler.decodeSigned, RustWorkspace.Composite.reverse_result_ok,
      Lynx.Rustler.encodeResult, Lynx.Rustler.encodeSigned, Erlang.erlang.«==/2»] <;> norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
    """

  law result_narrows_u8,
    expects: LynxRustFixture.CompositeNative.reverse_result({:error, 256}) == {:ok, 0},
    proof: ~LEAN"""
    simp [«result_narrows_u8:ensures/0», Elixir.LynxRustFixture.CompositeNative.«reverse_result/1»,
      Elixir.LynxRustFixture.CompositeNative.«reverse_result:execution/1»,
      Lynx.Rustler.decodeResult, Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField,
      Lynx.Rustler.decodeUnsigned, RustWorkspace.Composite.reverse_result_err,
      Lynx.Rustler.encodeResult, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»]
    """

  law nested_tuples,
    expects:
      LynxRustFixture.CompositeNative.echo_nested({{true}, {256, -1, {}}}) ==
        {{true}, {0, -1, {}}},
    proof: ~LEAN"""
    simp [«nested_tuples:ensures/0», Elixir.LynxRustFixture.CompositeNative.«echo_nested/1»,
      Elixir.LynxRustFixture.CompositeNative.«echo_nested:execution/1»,
      Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeBool,
      Lynx.Rustler.decodeUnsigned, Lynx.Rustler.decodeSigned, RustWorkspace.Composite.nested_identity,
      Lynx.Rustler.encodeBool, Lynx.Rustler.encodeUnsigned, Lynx.Rustler.encodeSigned,
      Erlang.erlang.«==/2»] <;> norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
    """

  law seven_fields,
    expects:
      LynxRustFixture.CompositeNative.echo_seven({1, 2, 3, 4, 5, 6, 256}) == {1, 2, 3, 4, 5, 6, 0},
    proof: ~LEAN"""
    simp [«seven_fields:ensures/0», Elixir.LynxRustFixture.CompositeNative.«echo_seven/1»,
      Elixir.LynxRustFixture.CompositeNative.«echo_seven:execution/1»,
      Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField, Lynx.Rustler.decodeUnsigned,
      RustWorkspace.Composite.seven_identity, Lynx.Rustler.encodeUnsigned, Erlang.erlang.«==/2»] <;> norm_num [Aeneas.Std.IScalar.val, Aeneas.Std.UScalar.val, BitVec.toInt]
    """

  law rejects_tuple_shape,
    expects:
      (try do
         LynxRustFixture.CompositeNative.transform_pair({true, 1, 2})
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_tuple_shape:ensures/0», Elixir.LynxRustFixture.CompositeNative.«transform_pair/1»,
      Lynx.Rustler.decodeTuple, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law rejects_result_tag,
    expects:
      (try do
         LynxRustFixture.CompositeNative.reverse_result({:other, 5})
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_result_tag:ensures/0», Elixir.LynxRustFixture.CompositeNative.«reverse_result/1»,
      Lynx.Rustler.decodeResult, Lynx.Rustler.decodeTuple, Lynx.Rustler.tupleField,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
