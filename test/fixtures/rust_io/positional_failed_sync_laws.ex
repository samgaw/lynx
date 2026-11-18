defmodule LynxPositionalFixture.FailedSync do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law failed_sync_leaves_write_visible,
    expects:
      (
        writer = :erlang.get(:writer)
        acknowledged = Native.patch_at(writer, 0, 9)
        observed = Native.observe_at(writer, 0)
        acknowledged == false and observed == 9
      ),
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 64)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end
