defmodule LynxAtomicFixture.FalseLaws do
  @compile :debug_info
  use Lynx.Laws

  # This is deliberately false: creation stores seven and no update occurs.
  law wrong_readback,
    expects: LynxAtomicFixture.Native.atomic_read(LynxAtomicFixture.Native.atomic_new(7)) == 8,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
