defmodule LynxDecodedFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law updated,
    expects:
      (
        resource = LynxDecodedFixture.Native.atomic_new(7)
        returned = LynxDecodedFixture.Native.atomic_decoded(resource, 1, true) == 7
        returned and LynxDecodedFixture.Native.atomic_read(resource) == 9
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

  law read_only,
    expects:
      (
        resource = LynxDecodedFixture.Native.atomic_new(7)
        returned = LynxDecodedFixture.Native.atomic_decoded(resource, 0, true) == 7
        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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

  law disabled,
    expects:
      (
        resource = LynxDecodedFixture.Native.atomic_new(7)
        returned = LynxDecodedFixture.Native.atomic_decoded(resource, 1, false) == 7
        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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

  law range,
    expects:
      (
        resource = LynxDecodedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDecodedFixture.Native.atomic_decoded(resource, -1, true)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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
        resource = LynxDecodedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDecodedFixture.Native.atomic_decoded(resource, 2, true)
            false
          catch
            :error, :nif_panicked -> true
          end

        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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
        resource = LynxDecodedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDecodedFixture.Native.atomic_decoded(resource, 3, true)
            false
          catch
            :error, :rust_panicked -> true
          end

        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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
        resource = LynxDecodedFixture.Native.atomic_new(7)

        returned =
          LynxDecodedFixture.Native.atomic_decoded(resource, 4, true) == :decoder_rejected

        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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
        resource = LynxDecodedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDecodedFixture.Native.atomic_decoded(resource, 5, true)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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

  law later_failure,
    expects:
      (
        resource = LynxDecodedFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDecodedFixture.Native.atomic_decoded(resource, 1, :invalid)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxDecodedFixture.Native.atomic_read(resource) == 7
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

  law first_failure_wins,
    expects: LynxDecodedFixture.Native.atomic_decoded_first(4, :invalid) == :decoder_rejected,
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
        resource = LynxDecodedFixture.Native.atomic_new(18_446_744_073_709_551_615)

        LynxDecodedFixture.Native.atomic_decoded_first(1, resource) == 18_446_744_073_709_551_615 and
          LynxDecodedFixture.Native.atomic_read(resource) == 1
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
