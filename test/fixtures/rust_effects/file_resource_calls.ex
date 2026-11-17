defmodule LynxEffectsFixture.FileCalls do
  @compile :debug_info
  use Lynx.Laws

  law release_then_sync,
    expects:
      (
        resource = :erlang.get(:file)

        LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law sync_release_sync,
    expects:
      (
        resource = :erlang.get(:file)

        LynxFileResourceFixture.Native.file_sync(resource) and
          LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law rejects_integer_sync(input),
    requires: is_integer(input),
    expects:
      (try do
         LynxFileResourceFixture.Native.file_sync(input)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    cases input <;> simp_all [«rejects_integer_sync:requires/1», Erlang.erlang.«is_integer/1»]
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
