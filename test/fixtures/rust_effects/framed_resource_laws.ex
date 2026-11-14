defmodule LynxEffectsFixture.FramedResourceLaws do
  @compile :debug_info
  use Lynx.Laws

  law update_preserves_other,
    expects:
      (
        resource = :erlang.get(:counter)
        other = :erlang.get(:other)

        LynxEffectsFixture.Native.counter_add(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 10 and
          LynxEffectsFixture.Native.counter_value(other) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Shared.Properties.Framed.accepted 10#u64) 256
        (.start Shared.Properties.Framed.initial
          (Lynx.apply «update_preserves_other:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.Properties.Framed.accepted_outcome 10#u64 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxEffectsFixture.FramedResourceOverflowLaws do
  @compile :debug_info
  use Lynx.Laws

  law overflow_preserves_other,
    expects:
      (
        resource = :erlang.get(:counter)
        other = :erlang.get(:other)

        not LynxEffectsFixture.Native.counter_add(resource, 1) and
          LynxEffectsFixture.Native.counter_value(resource) == 18_446_744_073_709_551_615 and
          LynxEffectsFixture.Native.counter_value(other) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Shared.Properties.Framed.accepted 18446744073709551615#u64) 256
        (.start Shared.Properties.Framed.overflowInitial
          (Lynx.apply «overflow_preserves_other:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.Properties.Framed.accepted_outcome 18446744073709551615#u64 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end
