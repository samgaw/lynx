defmodule LynxIoFixture.ReopenedLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law repaired_resource,
    expects: is_reference(LynxIoFixture.Native.log_reopen(2)),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.ReopenedLogProperties.accepted_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 512) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end
