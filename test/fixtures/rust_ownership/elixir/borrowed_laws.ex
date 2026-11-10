defmodule LynxBorrowedOwnershipFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law flips_true,
    expects: LynxBorrowedOwnershipFixture.Native.borrowed_flip(true) == false,
    proof: ~LEAN"""
    simp [«flips_true:ensures/0», Elixir.LynxBorrowedOwnershipFixture.Native.«borrowed_flip/1»,
      Elixir.LynxBorrowedOwnershipFixture.Native.«borrowed_flip:execution/1»,
      Borrowed.Properties.facade, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law flips_false,
    expects: LynxBorrowedOwnershipFixture.Native.borrowed_flip(false) == true,
    proof: ~LEAN"""
    simp [«flips_false:ensures/0», Elixir.LynxBorrowedOwnershipFixture.Native.«borrowed_flip/1»,
      Elixir.LynxBorrowedOwnershipFixture.Native.«borrowed_flip:execution/1»,
      Borrowed.Properties.facade, Lynx.Rustler.decodeBool, Lynx.Rustler.encodeBool,
      Erlang.erlang.«==/2»]
    """

  law rejects_non_boolean,
    expects:
      (try do
         LynxBorrowedOwnershipFixture.Native.borrowed_flip(7) == :badarg
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«rejects_non_boolean:ensures/0», Elixir.LynxBorrowedOwnershipFixture.Native.«borrowed_flip/1»,
      Lynx.Rustler.decodeBool, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
