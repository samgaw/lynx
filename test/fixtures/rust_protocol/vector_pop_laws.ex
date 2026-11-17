defmodule __MODULE__.Laws do
  @compile :debug_info
  use Lynx.Laws

  @proof ~LEAN"""
  cbv
  simp only [__MODULE__.Boundary.records_decoded, __MODULE__.Boundary.bounds_decoded,
    __MODULE__.Boundary.singleton_decoded, __MODULE__.Boundary.bad_head,
    __MODULE__.Boundary.out_of_range, __MODULE__.Boundary.improper,
    Lynx.Rustler.decodeScalarVec_nil]
  cbv
  """

  law last_record, expects: __MODULE__.Native.pop_record([-1, 42]) == {42, [-1]}, proof: @proof
  law empty, expects: __MODULE__.Native.pop_record([]) == {nil, []}, proof: @proof
  law singleton, expects: __MODULE__.Native.pop_record([0]) == {0, []}, proof: @proof

  law signed_bounds,
    expects:
      __MODULE__.Native.pop_record([-9_223_372_036_854_775_808, 9_223_372_036_854_775_807]) ==
        {9_223_372_036_854_775_807, [-9_223_372_036_854_775_808]},
    proof: @proof

  law invalid_record,
    expects:
      (try do
         __MODULE__.Native.pop_record([false])
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law out_of_range,
    expects:
      (try do
         __MODULE__.Native.pop_record([9_223_372_036_854_775_808])
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law bad_head_before_tail,
    expects:
      (try do
         __MODULE__.Native.pop_record([false | 7])
         false
       rescue
         ArgumentError -> true
       end),
    proof: @proof

  law improper_tail,
    expects:
      (try do
         __MODULE__.Native.pop_record([0 | 7])
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: @proof
end
