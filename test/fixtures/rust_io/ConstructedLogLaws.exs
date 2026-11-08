defmodule LynxIoFixture.ConstructedLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law create_append,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_create(), 13) == true,
    proof: ~LEAN"""
    simp only [Lynx.concurrentFrom_eq_run, Lynx.apply_eq, «create_append:ensures/0»]
    change ((_ : Lynx.Result).run (Record.ConstructorLogProperties.initial
      {} Record.ConstructedLogProperties.input.script) schedule).1 = _
    rw [Record.ConstructorAdapterProperties.create_run]
    rw [Record.ConstructorAdapterProperties.append_run]
    simp [Erlang.erlang.«==/2», Lynx.Result.ofExcept]
    """
end
