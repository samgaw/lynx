defmodule LynxPositionalFixture.Restarted do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law reads_reopened_byte,
    expects:
      (
        resource = Native.open_slots()
        Native.observe_at(resource, 0) == 7
      ),
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 64)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
