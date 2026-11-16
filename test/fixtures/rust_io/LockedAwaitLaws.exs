defmodule LynxLockedAwaitFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxLockedAwaitFixture.Native

  law cancel_then_resume,
    expects:
      (
        owner = Native.async_log_open()
        one = Native.async_log_write(owner, 7, 8, false)
        two = Native.async_log_write(owner, 9, 10, true)

        one == {:ok, nil} and
          two == {:ok, 2} and
          Native.async_log_read(owner, 0) == {:ok, 2055} and
          Native.async_log_read(owner, 2) == {:ok, 2569}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 32768 in
    set_option maxHeartbeats 24000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 2048)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """

  law resume_then_cancel,
    expects:
      (
        owner = Native.async_log_open()
        one = Native.async_log_write(owner, 7, 8, true)
        two = Native.async_log_write(owner, 9, 10, false)

        one == {:ok, 2} and
          two == {:ok, nil} and
          Native.async_log_read(owner, 0) == {:ok, 2055} and
          Native.async_log_read(owner, 2) == {:ok, 2569}
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 32768 in
    set_option maxHeartbeats 24000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 2048)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end

defmodule LynxLockedAwaitFixture.ErrorLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxLockedAwaitFixture.Native

  law opening_failure,
    expects: Native.async_log_open() == :open_failed,
    proof: ~LEAN"""
    set_option maxRecDepth 32768 in
    set_option maxHeartbeats 24000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 2048)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    set_option cbv.maxSteps 24000000 in cbv
    """
end

defmodule LynxLockedAwaitFixture.ConcurrentLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxLockedAwaitFixture.Native

  law concurrent_cancel_and_resume,
    expects:
      (
        owner = Native.async_log_open()
        parent = self()

        spawn(fn ->
          send(parent, Native.async_log_write(owner, 7, 8, false))
        end)

        completed = Native.async_log_write(owner, 9, 10, true)

        receive do
          cancelled ->
            first = Native.async_log_read(owner, 0)
            second = Native.async_log_read(owner, 2)

            cancelled == {:ok, nil} and completed == {:ok, 2} and
              ((first == {:ok, 2055} and second == {:ok, 2569}) or
                 (first == {:ok, 2569} and second == {:ok, 2055}))
        end
      ),
    proof: ~LEAN"""
    set_option maxRecDepth 32768 in
    set_option maxHeartbeats 64000000 in
    refine ⟨1, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    cases depth with
    | zero => omega
    | succ depth =>
      apply terminal.outcome_eq.symm.trans
      apply Lynx.Outcome.eq_of_isTrue
      apply Lynx.Concurrent.checkPost_sound (depth := 2048)
        (accept := fun config => config.outcome.isTrue) ?_ run terminal
      clear enough events last outcome run terminal
      simp only [Lynx.apply_eq, «concurrent_cancel_and_resume:ensures/0», Erlang.program.fun_table,
        «-concurrent_cancel_and_resume:ensures/0-fun-0-/2»,
        Native.«async_log_write/4», Native.«async_log_write:execution/4»,
        LockedAwait.NifProperties.write_contract, LockedAwait.Properties.caller_contract,
        Lynx.NativeM.castUsizeU64_eq]
      lynx_check_post
    """
end
