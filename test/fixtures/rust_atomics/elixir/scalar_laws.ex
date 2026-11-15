defmodule LynxScalarFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law echo_bool,
    expects: LynxScalarFixture.Native.scalar_bool({false}) == false,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.bool_decoded (.atom "false") (false) (by rfl)
    simp only [Lynx.apply, «echo_bool:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_bool/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_i8,
    expects: LynxScalarFixture.Native.scalar_i8({255}) == -1,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.i8_decoded (.integer 255) ((-1)#i8) (by rfl)
    simp only [Lynx.apply, «echo_i8:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_i8/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_i16,
    expects: LynxScalarFixture.Native.scalar_i16({65535}) == -1,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.i16_decoded (.integer 65535) ((-1)#i16) (by rfl)
    simp only [Lynx.apply, «echo_i16:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_i16/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_i32,
    expects: LynxScalarFixture.Native.scalar_i32({-2_147_483_648}) == -2_147_483_648,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.i32_decoded (.integer (-2147483648)) ((-2147483648)#i32) (by rfl)
    simp only [Lynx.apply, «echo_i32:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_i32/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_i64,
    expects:
      LynxScalarFixture.Native.scalar_i64({-9_223_372_036_854_775_808}) ==
        -9_223_372_036_854_775_808,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.i64_decoded (.integer (-9223372036854775808)) ((-9223372036854775808)#i64) (by rfl)
    simp only [Lynx.apply, «echo_i64:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_i64/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_u8,
    expects: LynxScalarFixture.Native.scalar_u8({256}) == 0,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.u8_decoded (.integer 256) (0#u8) (by rfl)
    simp only [Lynx.apply, «echo_u8:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_u8/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_u16,
    expects: LynxScalarFixture.Native.scalar_u16({65537}) == 1,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.u16_decoded (.integer 65537) (1#u16) (by rfl)
    simp only [Lynx.apply, «echo_u16:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_u16/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_u32,
    expects: LynxScalarFixture.Native.scalar_u32({4_294_967_295}) == 4_294_967_295,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.u32_decoded (.integer 4294967295) (4294967295#u32) (by rfl)
    simp only [Lynx.apply, «echo_u32:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_u32/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law echo_u64,
    expects:
      LynxScalarFixture.Native.scalar_u64({18_446_744_073_709_551_615}) ==
        18_446_744_073_709_551_615,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.u64_decoded (.integer 18446744073709551615) (18446744073709551615#u64) (by rfl)
    simp only [Lynx.apply, «echo_u64:ensures/0», Elixir.LynxScalarFixture.Native.«scalar_u64/1», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mixed_update,
    expects:
      (
        resource = LynxScalarFixture.Native.atomic_new(0)

        returned =
          LynxScalarFixture.Native.atomic_scalar(resource, {true, 5, 65537}) == {5, 1, true, 0}

        returned and LynxScalarFixture.Native.atomic_read(resource) == 1
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.request_decoded true (.integer 5) (.integer 65537) 5#i8 1#u16 (by rfl) (by rfl)
    simp only [Lynx.Rustler.encodeBool, Bool.false_eq_true, ↓reduceIte] at decoded
    simp only [Lynx.apply, «mixed_update:ensures/0», Elixir.LynxScalarFixture.Native.«atomic_scalar/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mixed_negative,
    expects:
      (
        resource = LynxScalarFixture.Native.atomic_new(0)

        returned =
          LynxScalarFixture.Native.atomic_scalar(resource, {true, 255, 65537}) ==
            {-1, 1, false, 0}

        returned and LynxScalarFixture.Native.atomic_read(resource) == 0
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.request_decoded true (.integer 255) (.integer 65537) (-1)#i8 1#u16 (by rfl) (by rfl)
    simp only [Lynx.Rustler.encodeBool, Bool.false_eq_true, ↓reduceIte] at decoded
    simp only [Lynx.apply, «mixed_negative:ensures/0», Elixir.LynxScalarFixture.Native.«atomic_scalar/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mixed_disabled,
    expects:
      (
        resource = LynxScalarFixture.Native.atomic_new(0)

        returned =
          LynxScalarFixture.Native.atomic_scalar(resource, {false, 5, 65537}) == {5, 1, false, 0}

        returned and LynxScalarFixture.Native.atomic_read(resource) == 0
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.request_decoded false (.integer 5) (.integer 65537) 5#i8 1#u16 (by rfl) (by rfl)
    simp only [Lynx.Rustler.encodeBool, Bool.false_eq_true, ↓reduceIte] at decoded
    simp only [Lynx.apply, «mixed_disabled:ensures/0», Elixir.LynxScalarFixture.Native.«atomic_scalar/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mixed_mismatch,
    expects:
      (
        resource = LynxScalarFixture.Native.atomic_new(7)

        returned =
          LynxScalarFixture.Native.atomic_scalar(resource, {true, 5, 11}) == {5, 11, false, 7}

        returned and LynxScalarFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.request_decoded true (.integer 5) (.integer 11) 5#i8 11#u16 (by rfl) (by rfl)
    simp only [Lynx.Rustler.encodeBool, Bool.false_eq_true, ↓reduceIte] at decoded
    simp only [Lynx.apply, «mixed_mismatch:ensures/0», Elixir.LynxScalarFixture.Native.«atomic_scalar/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mixed_bad_signed,
    expects:
      (
        resource = LynxScalarFixture.Native.atomic_new(7)

        returned =
          try do
            LynxScalarFixture.Native.atomic_scalar(resource, {true, 2_147_483_648, 11})
            false
          catch
            :error, reason -> reason == "Could not decode field signed on Request"
          end

        returned and LynxScalarFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded := Scalars.Properties.request_signed_encoded true (.integer 2147483648) (.integer 11) (by rfl)
    simp only [Lynx.Rustler.encodeBool, Bool.false_eq_true, ↓reduceIte] at decoded
    simp only [Lynx.apply, «mixed_bad_signed:ensures/0», Elixir.LynxScalarFixture.Native.«atomic_scalar/2», decoded]
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
