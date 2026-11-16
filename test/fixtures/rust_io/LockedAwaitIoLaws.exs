defmodule LynxLockedAwaitIoFixture.ReadOnlyLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxLockedAwaitIoFixture.Native

  law failed_writes_keep_resource,
    expects:
      (
        owner = Native.async_log_readonly()
        cancelled = Native.async_log_write(owner, 7, 8, false)
        resumed = Native.async_log_write(owner, 9, 10, true)

        cancelled == {:ok, nil} and resumed == {:error, 1} and
          Native.async_log_read(owner, 0) == {:ok, 2055}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end

defmodule LynxLockedAwaitIoFixture.DecodeLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxLockedAwaitIoFixture.Native

  law bad_argument_preserves_failed_write,
    expects:
      (
        owner = Native.async_log_readonly()

        try do
          Native.async_log_write(owner, 4_294_967_296, 8, false)
          false
        rescue
          ArgumentError ->
            Native.async_log_write(owner, 7, 8, true) == {:error, 1} and
              Native.async_log_read(owner, 0) == {:ok, 2055}
        end
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end

defmodule LynxLockedAwaitIoFixture.PartialLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxLockedAwaitIoFixture.Native

  law cancelled_short_write_is_retained,
    expects:
      (
        owner = Native.async_log_open()
        cancelled = Native.async_log_write(owner, 7, 8, false)
        resumed = Native.async_log_write(owner, 9, 10, true)

        cancelled == {:ok, nil} and resumed == {:ok, 2} and
          Native.async_log_read(owner, 0) == {:ok, 2311} and
          Native.async_log_read(owner, 2) == {:ok, nil}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end
