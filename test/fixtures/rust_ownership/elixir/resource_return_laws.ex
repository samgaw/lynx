defmodule LynxResourceReturnFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law returns_true,
    expects:
      LynxResourceReturnFixture.Native.resource_checked(
        LynxResourceReturnFixture.Native.resource_allocate(true, true),
        true
      ) == true,
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law returns_false,
    expects:
      LynxResourceReturnFixture.Native.resource_checked(
        LynxResourceReturnFixture.Native.resource_allocate(false, true),
        true
      ) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law rejects_after_creation,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_allocate(true, false)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law rejects_first_argument,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_allocate(7, true)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law rejects_second_argument,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_allocate(true, 7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law rejects_later_decoding,
    expects:
      (try do
         LynxResourceReturnFixture.Native.resource_checked(
           LynxResourceReturnFixture.Native.resource_allocate(true, true),
           7
         )

         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law retains_handle,
    expects:
      (
        resource = LynxResourceReturnFixture.Native.resource_allocate(true, true)

        LynxResourceReturnFixture.Native.resource_checked(resource, true) == true and
          LynxResourceReturnFixture.Native.resource_checked(resource, true) == true
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law independent_handles,
    expects:
      (
        first = LynxResourceReturnFixture.Native.resource_allocate(true, true)
        second = LynxResourceReturnFixture.Native.resource_allocate(false, true)

        LynxResourceReturnFixture.Native.resource_checked(first, true) == true and
          LynxResourceReturnFixture.Native.resource_checked(second, true) == false
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law preserves_prior_handle,
    expects:
      (
        first = LynxResourceReturnFixture.Native.resource_allocate(true, true)

        try do
          LynxResourceReturnFixture.Native.resource_allocate(false, false)
          false
        catch
          :error, :nif_panicked ->
            LynxResourceReturnFixture.Native.resource_checked(first, true) == true
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end
