defmodule LynxIoFixture.UnsyncedRepairLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_then_failed_sync_then_retry,
    expects:
      (
        resource = :erlang.get(:log)

        rejected =
          try do
            LynxIoFixture.Native.log_repair_append(resource, -1, 0)
            false
          catch
            :error, :badarg -> true
          end

        rejected and not LynxIoFixture.Native.log_repair_append(resource, 4, 19) and
          LynxIoFixture.Native.log_repair_append(resource, 4, 23)
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost Record.UnsyncedRepairLogProperties.accepted 1024
        (.start Record.UnsyncedRepairLogProperties.initial
          (Lynx.apply «rejected_then_failed_sync_then_retry:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.UnsyncedRepairLogProperties.accepted_outcome last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end
