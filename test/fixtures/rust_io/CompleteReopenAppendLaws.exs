defmodule LynxIoFixture.CompleteReopenCommitLaws do
  @compile :debug_info
  use Lynx.Laws

  law commits_after_reopen,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_reopen(3), 29) == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.CompleteReopenAppend.append_law_outcome true last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end

defmodule LynxIoFixture.CompleteReopenRollbackLaws do
  @compile :debug_info
  use Lynx.Laws

  law rolls_back_after_reopen,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_reopen(3), 29) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.CompleteReopenAppend.append_law_outcome false last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end
