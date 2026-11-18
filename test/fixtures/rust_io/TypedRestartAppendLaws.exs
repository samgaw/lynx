defmodule LynxIoFixture.TypedRestartCommitLaws do
  @compile :debug_info
  use Lynx.Laws

  law checks_append_after_restart,
    expects: append() == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.TypedRestartAppend.law_outcome true last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp append() do
    reopened = LynxIoFixture.Native.log_try_reopen(3)
    LynxIoFixture.Native.log_append(reopened, 29)
  end
end

defmodule LynxIoFixture.TypedRestartRollbackLaws do
  @compile :debug_info
  use Lynx.Laws

  law checks_append_after_restart,
    expects: append() == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.TypedRestartAppend.law_outcome false last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp append() do
    reopened = LynxIoFixture.Native.log_try_reopen(3)
    LynxIoFixture.Native.log_append(reopened, 29)
  end
end
