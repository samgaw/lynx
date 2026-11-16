defmodule LynxGuardedSyncFixture.SuccessLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedSyncFixture.Native

  law cancelled_write_then_synchronized_prefix,
    expects:
      (
        owner = Native.async_log_open()
        cancelled = Native.async_log_sync(owner, 7, 8, false)
        resumed = Native.async_log_sync(owner, 9, 10, true)

        cancelled == {:ok, nil} and resumed == {:ok, 2} and
          Native.async_log_read(owner, 0) == {:ok, 2055} and
          Native.async_log_read(owner, 2) == {:ok, 2569}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end

defmodule LynxGuardedSyncFixture.FailureLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedSyncFixture.Native

  law failed_sync_retains_readable_writes,
    expects:
      (
        owner = Native.async_log_open()
        cancelled = Native.async_log_sync(owner, 7, 8, false)
        resumed = Native.async_log_sync(owner, 9, 10, true)

        cancelled == {:ok, nil} and resumed == {:error, 2} and
          Native.async_log_read(owner, 0) == {:ok, 2055} and
          Native.async_log_read(owner, 2) == {:ok, 2569}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end
