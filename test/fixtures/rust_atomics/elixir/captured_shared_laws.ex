defmodule LynxCapturedSharedFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxCapturedSharedFixture.Native

  law successive_frames,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 1, 7, 1, 0, 0>>)

        Native.shared_checked_frame(buffer, true) == {:ok, [1, 0, 1, 7]} and
          Native.shared_checked_frame(buffer, true) == {:ok, [1, 0, 0]} and
          Native.shared_read(buffer) == {0, 0}
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
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

  law rejected_consumes,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 1, 7, 1, 0, 0>>)

        try do
          Native.shared_checked_frame(buffer, false)
          false
        catch
          :error, :nif_panicked ->
            Native.shared_read(buffer) == {3, 1} and
              Native.shared_checked_frame(buffer, true) == {:ok, [1, 0, 0]} and
              Native.shared_read(buffer) == {0, 0}
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
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

  law incomplete_failure_retains,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 2, 8>>)

        try do
          Native.shared_checked_frame(buffer, false)
          false
        catch
          :error, :nif_panicked ->
            retained = Native.shared_read(buffer)
            Native.shared_append(buffer, <<9>>)

            retained == {4, 1} and
              Native.shared_checked_frame(buffer, true) == {:ok, [1, 0, 2, 8, 9]}
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
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

  law decoder_failure_preserves,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 0>>)

        try do
          Native.shared_checked_frame(buffer, :invalid)
          false
        rescue
          ArgumentError ->
            Native.shared_read(buffer) == {3, 1} and
              Native.shared_checked_frame(buffer, true) == {:ok, [1, 0, 0]}
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
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

  law malformed_preserves,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<2, 0, 0>>)

        Native.shared_checked_frame(buffer, true) == {:error, 1} and
          Native.shared_read(buffer) == {3, 2}
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
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
