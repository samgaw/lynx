defmodule __MODULE__.Laws do
  @compile :debug_info
  use Lynx.Laws

  @proof ~LEAN"""
  cbv
  simp only [__MODULE__.Properties.input_decoded, __MODULE__.Properties.boundary_decoded,
    __MODULE__.Properties.wrong_arity, __MODULE__.Properties.unsigned_range,
    __MODULE__.Properties.signed_range, __MODULE__.Properties.bad_head,
    __MODULE__.Properties.improper, __MODULE__.Properties.non_list,
    Lynx.Rustler.decodeScalarVec_nil]
  cbv
  """

  law update,
    expects:
      __MODULE__.Native.update_records([{-1, 18_446_744_073_709_551_615}, {42, 9}], 7) ==
        {true, [{7, 18_446_744_073_709_551_615}, {42, 9}]},
    proof: @proof

  law empty,
    expects: __MODULE__.Native.update_records([], -5) == {false, []},
    proof: @proof

  law signed_bounds,
    expects:
      __MODULE__.Native.update_records(
        [{-9_223_372_036_854_775_808, 0}],
        9_223_372_036_854_775_807
      ) ==
        {true, [{9_223_372_036_854_775_807, 0}]},
    proof: @proof

  law wrong_arity,
    expects:
      (try do
         __MODULE__.Native.update_records([{1}], 7)
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law unsigned_range,
    expects:
      (try do
         __MODULE__.Native.update_records([{0, 18_446_744_073_709_551_616}], 7)
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law signed_range,
    expects:
      (try do
         __MODULE__.Native.update_records([{9_223_372_036_854_775_808, 0}], 7)
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law non_list,
    expects:
      (try do
         __MODULE__.Native.update_records(:invalid, 7)
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law invalid_head_before_improper_tail,
    expects:
      (try do
         __MODULE__.Native.update_records([{:invalid, 0} | 7], 7)
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law improper_tail_panics,
    expects:
      (try do
         __MODULE__.Native.update_records([{1, 0} | 7], 7)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: @proof

  law first_argument_panics_before_second_argument,
    expects:
      (try do
         __MODULE__.Native.update_records([{1, 0} | 7], :invalid)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: @proof
end
