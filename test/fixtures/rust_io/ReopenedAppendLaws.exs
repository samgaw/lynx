defmodule LynxIoFixture.ReopenedAppendLaws do
  @compile :debug_info
  use Lynx.Laws

  law durable_append,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_reopen(2), 19) == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.ReopenedLogProperties.appended_law_outcome (success := true) last
    apply Lynx.Concurrent.checkPost_sound (depth := 768) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end

defmodule LynxIoFixture.ReopenedRollbackLaws do
  @compile :debug_info
  use Lynx.Laws

  law short_write_rollback,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_reopen(2), 19) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.ReopenedLogProperties.appended_law_outcome (success := false) last
    apply Lynx.Concurrent.checkPost_sound (depth := 768) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end
