defmodule LynxIoFixture.ConstructedLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law create_append,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_create(), 13) == true,
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth _
    apply Lynx.concurrentFrom_of_readyPrefix
    simp only [Lynx.apply_eq, «create_append:ensures/0»]
    simpa [Lynx.Result.ofExcept, Erlang.erlang.«==/2», Record.ConstructedLogProperties.initial] using
      Record.ConstructorAdapterProperties.create_append_prefix (Lynx.Dispatcher.ofTable [] depth) {}
        (fun result => Lynx.Result.ofExcept (Erlang.erlang.«==/2» result (.atom "true")))
    """
end
