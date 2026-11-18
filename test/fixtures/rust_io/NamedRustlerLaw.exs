defmodule LynxIoFixture.NamedRepairLaws do
  @compile :debug_info
  use Lynx.Laws

  law repairs_three_acknowledged_records,
    expects: is_reference(LynxIoFixture.Native.log_try_reopen(5)),
    proof: ~LEAN"""
    set_option maxHeartbeats 64000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.NamedRustlerLaw.law_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 96) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end

defmodule LynxIoFixture.NamedRepairErrorLaws do
  @compile :debug_info
  use Lynx.Laws

  law reports_io_error_after_failed_close,
    expects: failure() == :journal_io,
    proof: ~LEAN"""
    set_option maxHeartbeats 64000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.NamedRustlerLaw.error_law_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 64) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp failure() do
    try do
      LynxIoFixture.Native.log_try_reopen(5)
      :unexpected
    catch
      :error, reason -> reason
    end
  end
end
