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
    set_option maxRecDepth 4096 in
    have verified : Lynx.Concurrent.check
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 192
        (.start {} (Lynx.apply «concurrent_update:ensures/0» Erlang.program.fun_table)) = true := by
      clear schedule
      as_aux_lemma =>
        simp only [Lynx.apply, «concurrent_update:ensures/0»,
          Elixir.LynxEffectsFixture.Native.«counter_new/1»,
          Elixir.LynxEffectsFixture.Native.«counter_add/2»,
          Elixir.LynxEffectsFixture.Native.«counter_value/1»,
          Lynx.Rustler.withResourceTypes, bind_assoc, Lynx.Result.nativeModify_bind]
        set_option cbv.maxSteps 8000000 in cbv
    have checked := Lynx.concurrent_of_check
      (Lynx.apply «concurrent_update:ensures/0» Erlang.program.fun_table)
      (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 192 verified schedule
    have accepted (outcome : Lynx.Outcome Lynx.Term)
        (valid : (match outcome with | .ok (Lynx.Term.atom "true") => true | _ => false) = true) :
        outcome = .ok (Lynx.Term.atom "true") := by
      split at valid
      · rfl
      · contradiction
    exact accepted _ checked
    """
end
