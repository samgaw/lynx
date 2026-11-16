defmodule LynxGuardedRecoveryFixture.FirstFailureLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law report_first_read_failure,
    expects: Native.async_log_recover() == {:error, 1},
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

defmodule LynxGuardedRecoveryFixture.SecondFailureLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law report_second_read_failure,
    expects: Native.async_log_recover() == {:error, 1},
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

defmodule LynxGuardedRecoveryFixture.TailLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxGuardedRecoveryFixture.Native

  law recover_partial_final_word,
    expects: Native.async_log_recover() == {:ok, {2055, nil}},
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
