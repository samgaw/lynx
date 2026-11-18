defmodule LynxIoFixture.MixedRepairAppendLaws do
  @compile :debug_info
  use Lynx.Laws

  law commits_after_two_interruptions,
    expects: append() == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.MixedRepairAppend.committed_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp append() do
    reopened = LynxIoFixture.Native.log_try_reopen(3)
    LynxIoFixture.Native.log_append(reopened, 29)
  end
end
