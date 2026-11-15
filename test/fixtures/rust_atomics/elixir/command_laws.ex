defmodule LynxCommandFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law read,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        LynxCommandFixture.Native.atomic_command(resource, :read) == {false, 7} and
          LynxCommandFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Commands.Properties.read_decoded
    simp only [Lynx.apply, «read:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law compare,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        LynxCommandFixture.Native.atomic_command(resource, {:compare, {7, 11}}) == {true, 7} and
          LynxCommandFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Commands.Properties.compare_decoded (.tuple #[.integer 7, .integer 11]) _ (Commands.Properties.replacement_decoded 7#u64 11#u64)
    simp only [Lynx.apply, «compare:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mismatch,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        LynxCommandFixture.Native.atomic_command(resource, {:compare, {0, 11}}) == {false, 7} and
          LynxCommandFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Commands.Properties.compare_decoded (.tuple #[.integer 0, .integer 11]) _ (Commands.Properties.replacement_decoded 0#u64 11#u64)
    simp only [Lynx.apply, «mismatch:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law nested_rejection,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        returned =
          try do
            LynxCommandFixture.Native.atomic_command(resource, {:compare, 0})
            false
          catch
            :error, reason -> reason == "Could not decode field on position 1"
          end

        returned and LynxCommandFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Commands.Properties.nested_rejected_encoded (.integer 0) Commands.Properties.replacement_shape_rejected
    simp only [Lynx.apply, «nested_rejection:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law nested_first_field_rejection,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        returned =
          try do
            LynxCommandFixture.Native.atomic_command(resource, {:compare, {true, 11}})
            false
          catch
            :error, reason -> reason == "Could not decode field on position 1"
          end

        returned and LynxCommandFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have inner := Commands.Properties.replacement_expected_error (.atom "true") (.integer 11) (by rfl)
    have decoded := Commands.Properties.nested_error_encoded (.tuple #[.atom "true", .integer 11]) _ inner (Commands.Properties.string_error_disposed _)
    simp only [Lynx.apply, «nested_first_field_rejection:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law nested_second_field_rejection,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        returned =
          try do
            LynxCommandFixture.Native.atomic_command(resource, {:compare, {7, false}})
            false
          catch
            :error, reason -> reason == "Could not decode field on position 1"
          end

        returned and LynxCommandFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have inner := Commands.Properties.replacement_second_error 7#u64 (.atom "false") (by rfl)
    have decoded := Commands.Properties.nested_error_encoded (.tuple #[.integer 7, .atom "false"]) _ inner (Commands.Properties.string_error_disposed _)
    simp only [Lynx.apply, «nested_second_field_rejection:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law nested_range_rejection,
    expects:
      (
        resource = LynxCommandFixture.Native.atomic_new(7)

        returned =
          try do
            LynxCommandFixture.Native.atomic_command(
              resource,
              {:compare, {18_446_744_073_709_551_616, 11}}
            )

            false
          catch
            :error, reason -> reason == "Could not decode field on position 1"
          end

        returned and LynxCommandFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have inner := Commands.Properties.replacement_expected_error (.integer 18446744073709551616) (.integer 11) (by rfl)
    have decoded := Commands.Properties.nested_error_encoded (.tuple #[.integer 18446744073709551616, .integer 11]) _ inner (Commands.Properties.string_error_disposed _)
    simp only [Lynx.apply, «nested_range_rejection:ensures/0», Elixir.LynxCommandFixture.Native.«atomic_command/2», decoded]
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
