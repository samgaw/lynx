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
    refine ⟨1, ?_⟩
    intro depth enough
    obtain ⟨remaining, rfl⟩ : ∃ remaining, depth = remaining + 1 := ⟨depth - 1, by omega⟩
    intro elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost Record.ConcurrentRecoveryProperties.recoverable 384
        (.start Record.ConcurrentStorageProperties.initial
          (Lynx.apply «concurrent_append:ensures/0» Erlang.program.fun_table 1) elapsed) = true := by
      clear enough remaining events last outcome run terminal
      lynx_check_post
    have durable := Lynx.Concurrent.checkPost_sound verified run terminal
    have accepted := Record.ConcurrentRecoveryProperties.accepted_outcome last durable
    exact terminal.outcome_eq.symm.trans accepted
    """
end
