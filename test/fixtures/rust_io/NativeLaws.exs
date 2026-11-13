defmodule LynxIoFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law published,
    expects: LynxIoFixture.Native.commit(513) == true,
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth _
    apply Lynx.concurrentFrom_of_readyPrefix
    simp only [Lynx.apply_eq, «published:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept]
    exact (Publish.Native.adapter_prefix _ _ rfl rfl).bind
      (fun result => Lynx.Result.ofExcept (Erlang.erlang.«==/2» result Lynx.Term.true))
    """

  law bounded_publication(value),
    requires: is_integer(value) and value >= 0 and value < 65536,
    expects: LynxIoFixture.Native.commit(value) == true,
    proof: ~LEAN"""
    cases value <;> simp [«bounded_publication:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    have upper : number < (2 : Int) ^ 32 := range.2
    refine ⟨0, ?_⟩
    intro depth _
    apply Lynx.concurrentFrom_of_readyPrefix
    simp only [Lynx.apply_eq, «bounded_publication:ensures/1»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, range.1, upper, and_self, ite_true,
      Lynx.Result.ofExcept, Lynx.Result.ok_bind]
    exact (Publish.Native.adapter_prefix _ _ rfl rfl).bind
      (fun result => Lynx.Result.ofExcept (Erlang.erlang.«==/2» result Lynx.Term.true))
    """

  law negative,
    expects:
      (try do
         LynxIoFixture.Native.commit(-1)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«negative:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Lynx.Rustler.decodeUnsigned,
      Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law too_large,
    expects:
      (try do
         LynxIoFixture.Native.commit(4_294_967_296)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«too_large:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Lynx.Rustler.decodeUnsigned,
      Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """

  law wrong_type,
    expects:
      (try do
         LynxIoFixture.Native.commit(false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [«wrong_type:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Lynx.Rustler.decodeUnsigned,
      Lynx.Result.ofExcept, Lynx.Result.tryWith, Lynx.Result.handle, Lynx.Result.bind,
      Lynx.Exception.classTerm, Lynx.Exception.reason]
    """
end
