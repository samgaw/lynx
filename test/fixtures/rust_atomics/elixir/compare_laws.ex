defmodule LynxCompareFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law matched_update,
    expects:
      (
        resource = LynxCompareFixture.Native.atomic_new(7)

        LynxCompareFixture.Native.atomic_replace(resource, 7, 11) == {true, 7} and
          LynxCompareFixture.Native.atomic_read(resource) == 11
      ),
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

  law mismatch_preserves,
    expects:
      (
        resource = LynxCompareFixture.Native.atomic_new(7)

        LynxCompareFixture.Native.atomic_replace(resource, 8, 11) == {false, 7} and
          LynxCompareFixture.Native.atomic_read(resource) == 7
      ),
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

  law decoder_cleanup,
    expects:
      (
        resource = LynxCompareFixture.Native.atomic_new(7)

        failed =
          try do
            LynxCompareFixture.Native.atomic_replace(resource, 7, -1)
            false
          catch
            :error, :badarg -> true
          end

        failed and LynxCompareFixture.Native.atomic_read(resource) == 7
      ),
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

  law competing_transitions,
    expects:
      (
        resource = LynxCompareFixture.Native.atomic_new(0)
        parent = self()
        spawn(fn -> send(parent, LynxCompareFixture.Native.atomic_replace(resource, 0, 1)) end)
        ours = LynxCompareFixture.Native.atomic_replace(resource, 0, 2)

        receive do
          theirs ->
            (ours == {true, 0} and theirs == {false, 2} and
               LynxCompareFixture.Native.atomic_read(resource) == 2) or
              (ours == {false, 1} and theirs == {true, 0} and
                 LynxCompareFixture.Native.atomic_read(resource) == 1)
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨2, ?_⟩
    intro depth enough
    obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' enough
    intro elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
