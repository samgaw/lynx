defmodule LynxEffectsFixture.ConcurrentResourceLaws do
  @compile :debug_info
  use Lynx.Laws

  law concurrent_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)
        parent = self()

        spawn(fn ->
          send(parent, {:updated, LynxEffectsFixture.Native.counter_add(resource, 3)})
        end)

        changed = LynxEffectsFixture.Native.counter_add(resource, 3)

        peer =
          receive do
            {:updated, result} -> result
          end

        changed and peer and LynxEffectsFixture.Native.counter_value(resource) == 13
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨1, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    cases depth with
    | zero => omega
    | succ depth =>
      have verified : Lynx.Concurrent.checkPost (fun config => config.outcome.isTrue) 256
          (.start {}
            (Lynx.apply «concurrent_update:ensures/0» Erlang.program.fun_table (depth + 1)) elapsed) = true := by
        clear enough events last outcome run terminal
        lynx_check_post
      have accepted := Lynx.Outcome.eq_of_isTrue
        (Lynx.Concurrent.checkPost_sound verified run terminal)
      exact terminal.outcome_eq.symm.trans accepted
    """
end
