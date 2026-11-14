defmodule LynxEffectsFixture.SharedLaws do
  @compile :debug_info
  use Lynx.Laws

  law shared_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        LynxEffectsFixture.Native.counter_add(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 10
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

  law overflow_preserves,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(18_446_744_073_709_551_615)

        LynxEffectsFixture.Native.counter_add(resource, 1) == false and
          LynxEffectsFixture.Native.counter_value(resource) == 18_446_744_073_709_551_615
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

  law decoder_cleanup,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        caught =
          try do
            LynxEffectsFixture.Native.counter_add(resource, false)
            false
          catch
            :error, :badarg -> true
          end

        caught and LynxEffectsFixture.Native.counter_value(resource) == 7
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
