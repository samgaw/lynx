defmodule LynxIoFixture.ConcurrentLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law concurrent_append,
    expects:
      (
        resource = LynxIoFixture.Native.log_create()
        parent = self()

        spawn(fn ->
          send(parent, {:appended, LynxIoFixture.Native.log_append(resource, 19)})
        end)

        appended = LynxIoFixture.Native.log_append(resource, 13)

        peer =
          receive do
            {:appended, result} -> result
          end

        appended and peer
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 64000000 in
    set_option maxRecDepth 4096 in
    have verified : Lynx.Concurrent.checkPost Record.ConcurrentStorageProperties.durableRecords 384
        (.start Record.ConcurrentStorageProperties.initial
          (Lynx.apply «concurrent_append:ensures/0» Erlang.program.fun_table)) = true := by
      clear schedule
      as_aux_lemma =>
        simp only [Lynx.apply, «concurrent_append:ensures/0»,
          Elixir.LynxIoFixture.Native.«log_create/0»,
          Elixir.LynxIoFixture.Native.«log_append/2»,
          Lynx.Rustler.withResourceTypes, bind_assoc, Lynx.Result.nativeModify_bind]
        set_option cbv.maxSteps 32000000 in cbv
    obtain ⟨events, last, run, terminal⟩ := Lynx.Result.run_reaches
      (Lynx.apply «concurrent_append:ensures/0» Erlang.program.fun_table)
      Record.ConcurrentStorageProperties.initial schedule
    have durable := Lynx.Concurrent.checkPost_sound verified run terminal
    have accepted := Record.ConcurrentStorageProperties.accepted_outcome last durable
    rw [terminal.outcome_eq] at accepted
    simpa only [Lynx.concurrentFrom_eq_run] using accepted
    """
end
