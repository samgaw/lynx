defmodule LynxGuardedRecoveryFixture.WriterLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law acknowledged_prefix,
    expects:
      (
        owner = Native.async_log_open()
        cancelled = Native.async_log_sync(owner, 7, 8, false)
        resumed = Native.async_log_sync(owner, 9, 10, true)
        cancelled == {:ok, nil} and resumed == {:ok, 2}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 16000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end

defmodule LynxGuardedRecoveryFixture.CompleteLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law recover_acknowledged_words,
    expects: Native.async_log_recover() == {:ok, {2055, 2569}},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 16000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end

defmodule LynxGuardedRecoveryFixture.TruncatedLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law reject_truncated_words,
    expects: Native.async_log_recover() == {:ok, {nil, nil}},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 16000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end

defmodule LynxGuardedRecoveryFixture.DeniedLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law report_open_failure,
    expects: Native.async_log_recover() == {:error, 3},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 16000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 32000000 in cbv
    """
end
