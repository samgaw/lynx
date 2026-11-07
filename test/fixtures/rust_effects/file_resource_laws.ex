defmodule LynxEffectsFixture.FileResourceLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejects_integer_resource(input),
    requires: is_integer(input),
    expects:
      (try do
         LynxFileResourceFixture.Native.file_release(input)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    cases input <;> simp_all [«rejects_integer_resource:requires/1», Erlang.erlang.«is_integer/1»]
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «rejects_integer_resource:ensures/1»,
      Elixir.LynxFileResourceFixture.Native.«file_release/1», Lynx.Rustler.withResourceTypes,
      Lynx.Result.tryWith_eq, Lynx.Result.handle_get, Lynx.Result.handle_set, Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Lynx.NativeResourceArc.decode_nonreference_handled_next _ (by intro identity; simp)]
    simp [Lynx.Result.ok_bind, Lynx.Result.ok_apply, Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
