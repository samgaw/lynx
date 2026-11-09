defmodule LynxEffectsFixture.SharedLaws do
  @compile :debug_info
  use Lynx.Laws

  law shared_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        LynxEffectsFixture.Native.counter_add(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 10
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 4096 in
    have checked := Lynx.concurrent_of_check
      (Lynx.apply «shared_update:ensures/0» [])
      (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 128
      (by
        set_option maxHeartbeats 4000000 in
        set_option cbv.maxSteps 2000000 in cbv) schedule
    have accepted (outcome : Lynx.Outcome Lynx.Term)
        (valid : (match outcome with | .ok (Lynx.Term.atom "true") => true | _ => false) = true) :
        outcome = .ok (Lynx.Term.atom "true") := by
      split at valid
      · rfl
      · contradiction
    exact accepted _ checked
    """

  law overflow_preserves,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(18_446_744_073_709_551_615)

        LynxEffectsFixture.Native.counter_add(resource, 1) == false and
          LynxEffectsFixture.Native.counter_value(resource) == 18_446_744_073_709_551_615
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 4096 in
    have checked := Lynx.concurrent_of_check
      (Lynx.apply «overflow_preserves:ensures/0» [])
      (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 128
      (by
        set_option maxHeartbeats 4000000 in
        set_option cbv.maxSteps 2000000 in cbv) schedule
    have accepted (outcome : Lynx.Outcome Lynx.Term)
        (valid : (match outcome with | .ok (Lynx.Term.atom "true") => true | _ => false) = true) :
        outcome = .ok (Lynx.Term.atom "true") := by
      split at valid
      · rfl
      · contradiction
    exact accepted _ checked
    """

  law decoder_cleanup,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        caught =
          try do
            LynxEffectsFixture.Native.counter_add(resource, false)
            false
          catch
            :error, :badarg -> true
          end

        caught and LynxEffectsFixture.Native.counter_value(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 4096 in
    have checked := Lynx.concurrent_of_check
      (Lynx.apply «decoder_cleanup:ensures/0» [])
      (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 128
      (by
        set_option maxHeartbeats 4000000 in
        set_option cbv.maxSteps 2000000 in cbv) schedule
    have accepted (outcome : Lynx.Outcome Lynx.Term)
        (valid : (match outcome with | .ok (Lynx.Term.atom "true") => true | _ => false) = true) :
        outcome = .ok (Lynx.Term.atom "true") := by
      split at valid
      · rfl
      · contradiction
    exact accepted _ checked
    """
end
