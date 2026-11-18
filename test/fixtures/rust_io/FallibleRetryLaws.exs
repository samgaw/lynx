defmodule LynxIoFixture.RecordLimitRetryLaws do
  @compile :debug_info
  use Lynx.Laws

  law retries_reopen,
    expects: is_reference(retry()),
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.FallibleRetry.law_outcome true last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp retry() do
    try do
      LynxIoFixture.Native.log_try_reopen(2)
      :unexpected
    catch
      :error, :record_limit -> LynxIoFixture.Native.log_try_reopen(3)
    end
  end
end

defmodule LynxIoFixture.JournalIoRetryLaws do
  @compile :debug_info
  use Lynx.Laws

  law retries_reopen,
    expects: is_reference(retry()),
    proof: ~LEAN"""
    set_option maxHeartbeats 32000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Record.FallibleRetry.law_outcome false last
    apply Lynx.Concurrent.checkPost_sound (depth := 128) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """

  defp retry() do
    try do
      LynxIoFixture.Native.log_try_reopen(2)
      :unexpected
    catch
      :error, :journal_io -> LynxIoFixture.Native.log_try_reopen(3)
    end
  end
end
