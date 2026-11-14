defmodule LynxEffectsFixture.FutureCancelLaws do
  @compile :debug_info
  use Lynx.Laws

  law cancelled_without_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        LynxEffectsFixture.Native.counter_poll_cancel(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
