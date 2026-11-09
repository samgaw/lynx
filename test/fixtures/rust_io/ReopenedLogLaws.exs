defmodule LynxIoFixture.ReopenedLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law repaired_resource,
    expects: is_reference(LynxIoFixture.Native.log_reopen(2)),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have verified : Lynx.Concurrent.checkPost Record.ReopenedLogProperties.lawAccepted 512
        (.start Record.ReopenedLogProperties.initial
          (Lynx.apply «repaired_resource:ensures/0» [])) = true := by
      clear schedule
      as_aux_lemma =>
        simp only [Lynx.apply, «repaired_resource:ensures/0»,
          Elixir.LynxIoFixture.Native.«log_reopen/1»,
          Lynx.Rustler.withResourceTypes, bind_assoc, Lynx.Result.nativeModify_bind]
        set_option cbv.maxSteps 32000000 in cbv
    obtain ⟨events, last, run, terminal⟩ := Lynx.Result.run_reaches
      (Lynx.apply «repaired_resource:ensures/0» [])
      Record.ReopenedLogProperties.initial schedule
    have accepted := Record.ReopenedLogProperties.accepted_outcome last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    rw [terminal.outcome_eq] at accepted
    simpa only [Lynx.concurrentFrom_eq_run] using accepted
    """
end
