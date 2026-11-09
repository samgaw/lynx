defmodule LynxIoFixture.ReopenedAppendLaws do
  @compile :debug_info
  use Lynx.Laws

  law durable_append,
    expects: LynxIoFixture.Native.log_append(LynxIoFixture.Native.log_reopen(2), 19) == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have verified : Lynx.Concurrent.checkPost (Record.ReopenedLogProperties.appendedLawAccepted true) 768
        (.start Record.ReopenedLogProperties.appendInitial
          (Lynx.apply «durable_append:ensures/0» [])) = true := by
      clear schedule
      as_aux_lemma =>
        simp only [Lynx.apply, «durable_append:ensures/0»,
          Elixir.LynxIoFixture.Native.«log_reopen/1»,
          Elixir.LynxIoFixture.Native.«log_append/2»,
          Lynx.Rustler.withResourceTypes, bind_assoc, Lynx.Result.nativeModify_bind]
        set_option cbv.maxSteps 32000000 in cbv
    obtain ⟨events, last, run, terminal⟩ := Lynx.Result.run_reaches
      (Lynx.apply «durable_append:ensures/0» [])
      Record.ReopenedLogProperties.appendInitial schedule
    have accepted := Record.ReopenedLogProperties.appended_law_outcome last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    rw [terminal.outcome_eq] at accepted
    simpa only [Lynx.concurrentFrom_eq_run] using accepted
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
    have verified : Lynx.Concurrent.checkPost (Record.ReopenedLogProperties.appendedLawAccepted false) 768
        (.start Record.ReopenedLogProperties.shortInitial
          (Lynx.apply «short_write_rollback:ensures/0» [])) = true := by
      clear schedule
      as_aux_lemma =>
        simp only [Lynx.apply, «short_write_rollback:ensures/0»,
          Elixir.LynxIoFixture.Native.«log_reopen/1»,
          Elixir.LynxIoFixture.Native.«log_append/2»,
          Lynx.Rustler.withResourceTypes, bind_assoc, Lynx.Result.nativeModify_bind]
        set_option cbv.maxSteps 32000000 in cbv
    obtain ⟨events, last, run, terminal⟩ := Lynx.Result.run_reaches
      (Lynx.apply «short_write_rollback:ensures/0» [])
      Record.ReopenedLogProperties.shortInitial schedule
    have accepted := Record.ReopenedLogProperties.appended_law_outcome last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    rw [terminal.outcome_eq] at accepted
    simpa only [Lynx.concurrentFrom_eq_run] using accepted
    """
end
