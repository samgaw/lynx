defmodule LynxIoFixture.MixedRepairRestartLaws do
  @compile :debug_info
  use Lynx.Laws

  law reopens_after_interrupted_resize,
    expects: is_reference(LynxIoFixture.Native.log_try_reopen(3)),
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.MixedRepairWitness.law_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 64) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end
