defmodule LynxIoFixture.RepairingLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law repairing_appends,
    expects:
      (
        resource = :erlang.get(:log)

        LynxIoFixture.Native.log_repair_append(resource, 4, 19) and
          LynxIoFixture.Native.log_repair_append(resource, 4, 23)
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost Record.RepairingLogProperties.accepted 768
        (.start Record.RepairingLogProperties.initial
          (Lynx.apply «repairing_appends:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.accepted_outcome last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxIoFixture.RepairingLimitLaws do
  @compile :debug_info
  use Lynx.Laws

  law recovery_limit,
    expects: LynxIoFixture.Native.log_repair_append(:erlang.get(:log), 0, 19) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Record.RepairingLogProperties.unchangedAccepted 8) 768
        (.start Record.RepairingLogProperties.limitInitial
          (Lynx.apply «recovery_limit:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.unchanged_outcome 8 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxIoFixture.RepairingErrorLaws do
  @compile :debug_info
  use Lynx.Laws

  law io_failure,
    expects: LynxIoFixture.Native.log_repair_append(:erlang.get(:log), 4, 19) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Record.RepairingLogProperties.unchangedAccepted 8) 768
        (.start Record.RepairingLogProperties.errorInitial
          (Lynx.apply «io_failure:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.unchanged_outcome 8 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxIoFixture.RepairingNegativeLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_argument,
    expects:
      (try do
         LynxIoFixture.Native.log_repair_append(:erlang.get(:log), -1, 19)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Record.RepairingLogProperties.unchangedAccepted 7) 768
        (.start Record.RepairingLogProperties.initial
          (Lynx.apply «rejected_argument:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.unchanged_outcome 7 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxIoFixture.RepairingOverflowLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_argument,
    expects:
      (try do
         LynxIoFixture.Native.log_repair_append(:erlang.get(:log), 4_294_967_296, 19)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Record.RepairingLogProperties.unchangedAccepted 7) 768
        (.start Record.RepairingLogProperties.initial
          (Lynx.apply «rejected_argument:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.unchanged_outcome 7 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxIoFixture.RepairingPayloadLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_argument,
    expects:
      (try do
         LynxIoFixture.Native.log_repair_append(:erlang.get(:log), 4, 4_294_967_296)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Record.RepairingLogProperties.unchangedAccepted 7) 768
        (.start Record.RepairingLogProperties.initial
          (Lynx.apply «rejected_argument:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.unchanged_outcome 7 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end

defmodule LynxIoFixture.RepairingHandleLaws do
  @compile :debug_info
  use Lynx.Laws

  law rejected_argument,
    expects:
      (try do
         LynxIoFixture.Native.log_repair_append(:wrong, 4, 19)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost (Record.RepairingLogProperties.unchangedAccepted 6) 768
        (.start Record.RepairingLogProperties.initial
          (Lynx.apply «rejected_argument:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Record.RepairingLogProperties.unchanged_outcome 6 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """
end
