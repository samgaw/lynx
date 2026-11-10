defmodule LynxRwContentionFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law competing_updates,
    expects:
      (
        resource = LynxRwContentionFixture.Native.shared_new(false)
        parent = self()

        spawn(fn ->
          LynxRwContentionFixture.Native.shared_update(resource)
          send(parent, :done)
        end)

        LynxRwContentionFixture.Native.shared_update(resource)

        receive do
          :done -> LynxRwContentionFixture.Native.shared_read(resource) == false
        end
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 4096 in
      set_option maxHeartbeats 16000000 in
        set_option cbv.maxSteps 8000000 in
          have checked : Lynx.Concurrent.check
              (fun | .ok (.atom "true") => true | _ => false) 128
              (.start {} (Lynx.apply «competing_updates:ensures/0» Erlang.program.fun_table)) = true := by
            clear schedule
            as_aux_lemma =>
              simp only [Lynx.apply, «competing_updates:ensures/0»,
                Elixir.LynxRwContentionFixture.Native.«shared_new/1»,
                Elixir.LynxRwContentionFixture.Native.«shared_update/1»,
                Elixir.LynxRwContentionFixture.Native.«shared_read/1»,
                Lynx.Rustler.withResourceTypes, bind_assoc, Lynx.Result.nativeModify_bind]
              cbv
          have accepted := Lynx.concurrent_of_check
            (Lynx.apply «competing_updates:ensures/0» Erlang.program.fun_table)
            (fun | .ok (.atom "true") => true | _ => false) 128 checked schedule
          have accept (outcome : Lynx.Outcome Lynx.Term)
              (h : (match outcome with | .ok (.atom "true") => true | _ => false) = true) :
              outcome = .ok Lynx.Term.true := by
            split at h
            · rfl
            · contradiction
          exact accept _ accepted
    """
end
