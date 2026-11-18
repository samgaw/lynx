defmodule LynxPositionalFixture.ExactWrite do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law acknowledged_range_is_readable,
    expects:
      (
        writer = :erlang.get(:writer)

        Native.patch_all_at(writer, 1, <<7, 8>>) and
          Native.observe_at(writer, 1) == 7 and
          Native.observe_at(writer, 2) == 8
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
