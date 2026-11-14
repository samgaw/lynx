defmodule LynxIoFixture.ConcurrentRepairLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law concurrent_durable_appends,
    expects:
      (
        parent = self()
        resource = :erlang.get(:log)

        spawn(fn ->
          send(parent, LynxIoFixture.Native.log_repair_append(resource, 4, 23))
        end)

        left = LynxIoFixture.Native.log_repair_append(resource, 4, 19)

        receive do
          right -> left and right
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 64000000 in
    set_option maxRecDepth 8192 in
    refine ⟨1, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    cases depth with
    | zero => omega
    | succ depth =>
      have verified : Lynx.Concurrent.checkPost Record.ConcurrentRepairLogProperties.accepted 512
          (.start Record.ConcurrentRepairLogProperties.initial
            (Lynx.apply «concurrent_durable_appends:ensures/0» Erlang.program.fun_table (depth + 1)) elapsed) = true := by
        clear enough events last outcome run terminal
        lynx_check_post
      have accepted := Record.ConcurrentRepairLogProperties.accepted_outcome last
        (Lynx.Concurrent.checkPost_sound verified run terminal)
      exact terminal.outcome_eq.symm.trans accepted
    """
end
