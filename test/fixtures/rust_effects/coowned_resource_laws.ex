defmodule LynxEffectsFixture.CoownedResourceLaws do
  @compile :debug_info
  use Lynx.Laws

  law shared_owners_survive,
    expects: LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), 3),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Shared.FramedTermAdapter.accepted 10#u64 46) 256
        (.start Shared.FramedTermAdapter.initial
          (Lynx.apply «shared_owners_survive:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.FramedTermAdapter.accepted_outcome 10#u64 46 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """

  law overflow_keeps_owners,
    expects:
      LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), 18_446_744_073_709_551_615) ==
        false,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Shared.FramedTermAdapter.accepted 7#u64 46) 256
        (.start Shared.FramedTermAdapter.initial
          (Lynx.apply «overflow_keeps_owners:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.FramedTermAdapter.accepted_outcome 7#u64 46 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """

  law badarg_keeps_owners,
    expects:
      (try do
         LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Shared.FramedTermAdapter.accepted 7#u64 45) 256
        (.start Shared.FramedTermAdapter.initial
          (Lynx.apply «badarg_keeps_owners:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.FramedTermAdapter.accepted_outcome 7#u64 45 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end
