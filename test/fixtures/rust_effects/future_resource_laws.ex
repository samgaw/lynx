defmodule LynxEffectsFixture.FutureCancelLaws do
  @compile :debug_info
  use Lynx.Laws

  law cancelled_without_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        LynxEffectsFixture.Native.counter_poll_cancel(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 4096 in
    have checked := Lynx.concurrent_of_check
      (Lynx.apply «cancelled_without_update:ensures/0» [])
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
