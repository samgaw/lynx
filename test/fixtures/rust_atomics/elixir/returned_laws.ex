defmodule LynxReturnedFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law success,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)
        returned = LynxReturnedFixture.Native.atomic_result(resource, 0) == 7
        returned and LynxReturnedFixture.Native.atomic_read(resource) == 8
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

  law badarg,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxReturnedFixture.Native.atomic_result(resource, 1)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxReturnedFixture.Native.atomic_read(resource) == 8
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

  law atom,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)
        returned = LynxReturnedFixture.Native.atomic_result(resource, 2) == :rejected
        returned and LynxReturnedFixture.Native.atomic_read(resource) == 8
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

  law marker,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxReturnedFixture.Native.atomic_result(resource, 3)
            false
          catch
            :error, :rust_panicked -> true
          end

        returned and LynxReturnedFixture.Native.atomic_read(resource) == 8
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

  law panic,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxReturnedFixture.Native.atomic_result(resource, 4)
            false
          catch
            :error, :nif_panicked -> true
          end

        returned and LynxReturnedFixture.Native.atomic_read(resource) == 8
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

  law denied,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxReturnedFixture.Native.atomic_result(resource, 5)
            false
          catch
            :error, :denied -> true
          end

        returned and LynxReturnedFixture.Native.atomic_read(resource) == 8
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

  law decoder,
    expects:
      (
        resource = LynxReturnedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxReturnedFixture.Native.atomic_result(resource, -1)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxReturnedFixture.Native.atomic_read(resource) == 7
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
end
