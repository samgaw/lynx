defmodule LynxIoFixture.RecordLimitLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejects_reopen,
    expects: failure() == :record_limit,
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
      LynxIoFixture.Native.log_try_reopen(2)
      :unexpected
    catch
      :error, reason -> reason
    end
  end
end

defmodule LynxIoFixture.JournalIoLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejects_reopen,
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
      LynxIoFixture.Native.log_try_reopen(2)
      :unexpected
    catch
      :error, reason -> reason
    end
  end
end
