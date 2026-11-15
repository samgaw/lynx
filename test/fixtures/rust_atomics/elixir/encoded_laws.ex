defmodule LynxEncodedNativeFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law ordered_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)
        returned = LynxEncodedNativeFixture.Native.atomic_reply(resource, 7, 11) == {7, 11}
        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «ordered_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mismatched_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)
        returned = LynxEncodedNativeFixture.Native.atomic_reply(resource, 8, 11) == {7, 7}
        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «mismatched_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law absent_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)
        returned = LynxEncodedNativeFixture.Native.atomic_reply_option(resource, 7, 0) == nil
        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 0
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «absent_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_option/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law present_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)
        returned = LynxEncodedNativeFixture.Native.atomic_reply_option(resource, 7, 11) == 11
        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «present_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_option/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law ok_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)

        returned =
          LynxEncodedNativeFixture.Native.atomic_reply_result(resource, 7, 11) == {:ok, {7, 11}}

        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «ok_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_result/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law error_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)

        returned =
          LynxEncodedNativeFixture.Native.atomic_reply_result(resource, 8, 11) == {:error, 7}

        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «error_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_result/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law tuple_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)

        returned =
          LynxEncodedNativeFixture.Native.atomic_reply_tuple(resource, 7, 11) == {{7, 11}, 11}

        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «tuple_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_tuple/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law checked_reply,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)
        returned = LynxEncodedNativeFixture.Native.atomic_reply_checked(resource, 7, 11) == 11
        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «checked_reply:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_checked/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law encoder_panic,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxEncodedNativeFixture.Native.atomic_reply_checked(resource, 7, 0)
            false
          catch
            :error, :nif_panicked -> true
          end

        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 0
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «encoder_panic:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_checked/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law returned_ok,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)

        returned =
          LynxEncodedNativeFixture.Native.atomic_reply_nif_result(resource, 7, 11) == {7, 11}

        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «returned_ok:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_nif_result/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law returned_error,
    expects:
      (
        resource = LynxEncodedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxEncodedNativeFixture.Native.atomic_reply_nif_result(
              resource,
              18_446_744_073_709_551_615,
              11
            )

            false
          catch
            :error, :rust_panicked -> true
          end

        returned and LynxEncodedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «returned_error:ensures/0»,
      Elixir.LynxEncodedNativeFixture.Native.«atomic_reply_nif_result/3»,
      Encoded.Properties.encoder_spec, Encoded.Properties.checked_spec]
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
