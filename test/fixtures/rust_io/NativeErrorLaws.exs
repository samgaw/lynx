defmodule LynxIoFixture.ErrorLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_creation(value),
    requires: is_integer(value) and value >= 0 and value < 65536,
    expects: LynxIoFixture.Native.commit(value) == false,
    proof: ~LEAN"""
    cases value <;> simp [«rejected_creation:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    have upper : number < (2 : Int) ^ 32 := range.2
    refine ⟨0, ?_⟩
    intro depth _
    apply Lynx.concurrentFrom_of_readyPrefix
    simp only [Lynx.apply_eq, «rejected_creation:ensures/1»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, range.1, upper, and_self, ite_true,
      Lynx.Result.ofExcept, Lynx.Result.ok_bind]
    exact (Publish.Native.rejected_adapter_prefix _ _ rfl rfl).bind
      (fun result => Lynx.Result.ofExcept (Erlang.erlang.«==/2» result Lynx.Term.false))
    """

  law rejected_creation_is_a_result,
    expects:
      (try do
         LynxIoFixture.Native.commit(513) == false
       catch
         :error, _ -> false
       end),
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth _
    apply Lynx.concurrentFrom_of_readyPrefix
    simp only [Lynx.apply_eq, «rejected_creation_is_a_result:ensures/0»,
      Elixir.LynxIoFixture.Native.«commit/1», Elixir.LynxIoFixture.Native.«commit:execution/1»,
      Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept]
    exact ((Publish.Native.rejected_adapter_prefix _ _ rfl rfl).bind
      (fun result => Lynx.Result.ofExcept (Erlang.erlang.«==/2» result Lynx.Term.false))).tryWith _ _
    """
end
