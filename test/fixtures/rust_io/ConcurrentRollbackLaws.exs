defmodule LynxIoFixture.ConcurrentRollbackLaws do
  @compile :debug_info
  use Lynx.Laws

  law one_acknowledged_append,
    expects:
      (
        parent = self()
        resource = :erlang.get(:log)

        spawn(fn ->
          send(parent, {:writer, LynxIoFixture.Native.log_append(resource, 23)})
        end)

        left = LynxIoFixture.Native.log_append(resource, 19)
        :erlang.put(:left_ack, left)

        right =
          receive do
            {:writer, reply} -> reply
          end

        :erlang.put(:right_ack, right)
        (left and not right) or (not left and right)
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 128000000 in
    set_option maxRecDepth 8192 in
    refine ⟨1, ?_⟩
    intro depth enough
    cases depth with
    | zero => omega
    | succ depth =>
      intro elapsed events last outcome run terminal
      apply terminal.outcome_eq.symm.trans
      apply Record.ConcurrentRollback.law_outcome last
      apply Lynx.Concurrent.checkPost_sound (depth := 256) ?_ run terminal
      clear enough events last outcome run terminal
      lynx_check_post
    """
end
