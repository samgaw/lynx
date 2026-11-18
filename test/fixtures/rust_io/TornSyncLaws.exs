defmodule LynxIoFixture.TornSyncFailureLaws do
  @compile :debug_info
  use Lynx.Laws

  law reports_sync_error,
    expects: failure() == :journal_io,
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.FallibleReopen.law_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 64) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp failure() do
    try do
      LynxIoFixture.Native.log_try_reopen(3)
      :unexpected
    catch
      :error, reason -> reason
    end
  end
end

defmodule LynxIoFixture.TornSyncRestartLaws do
  @compile :debug_info
  use Lynx.Laws

  law opens_after_restart,
    expects: is_reference(LynxIoFixture.Native.log_try_reopen(3)),
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.FallibleReopen.law_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 64) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end
