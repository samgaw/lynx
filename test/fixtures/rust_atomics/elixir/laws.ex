defmodule LynxAtomicFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law shared_sequence,
    expects:
      (
        resource = LynxAtomicFixture.Native.atomic_new(7)

        LynxAtomicFixture.Native.atomic_claim(resource) == 7 and
          LynxAtomicFixture.Native.atomic_pair(resource) == {8, 9} and
          LynxAtomicFixture.Native.atomic_read(resource) == 10
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

  law wraparound,
    expects:
      (
        resource = LynxAtomicFixture.Native.atomic_new(18_446_744_073_709_551_615)

        LynxAtomicFixture.Native.atomic_pair(resource) == {18_446_744_073_709_551_615, 0} and
          LynxAtomicFixture.Native.atomic_read(resource) == 1
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

  law accepted_request,
    expects: LynxAtomicFixture.Native.atomic_checked(7, true) == {7, 8},
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

  law rejected_request,
    expects:
      (try do
         LynxAtomicFixture.Native.atomic_checked(7, false)
         false
       catch
         :error, :nif_panicked -> true
       end),
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

  law invalid_resource,
    expects:
      (try do
         LynxAtomicFixture.Native.atomic_claim(7)
         false
       catch
         :error, :badarg -> true
       end),
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

  law integer_boundaries,
    expects:
      (
        negative =
          try do
            LynxAtomicFixture.Native.atomic_new(-1)
            false
          catch
            :error, :badarg -> true
          end

        large =
          try do
            LynxAtomicFixture.Native.atomic_new(18_446_744_073_709_551_616)
            false
          catch
            :error, :badarg -> true
          end

        negative and large
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

  law competing_tickets,
    expects:
      (
        resource = LynxAtomicFixture.Native.atomic_new(18_446_744_073_709_551_615)
        parent = self()
        spawn(fn -> send(parent, LynxAtomicFixture.Native.atomic_claim(resource)) end)
        ours = LynxAtomicFixture.Native.atomic_claim(resource)

        receive do
          theirs ->
            ((ours == 0 and theirs == 18_446_744_073_709_551_615) or
               (ours == 18_446_744_073_709_551_615 and theirs == 0)) and
              LynxAtomicFixture.Native.atomic_read(resource) == 1
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
