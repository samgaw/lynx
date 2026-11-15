defmodule LynxSharedFrameFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxSharedFrameFixture.Native

  law successive_frames,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 1, 7, 1, 0, 0>>)
        first = Native.shared_frame(buffer)
        second = Native.shared_frame(buffer)
        first == {2, 4, 3} and second == {2, 3, 0} and Native.shared_read(buffer) == {0, 0}
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law incomplete_then_complete,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 2, 8>>)
        incomplete = Native.shared_frame(buffer)
        retained = Native.shared_read(buffer)
        Native.shared_append(buffer, <<9>>)

        incomplete == {0, 0, 4} and retained == {4, 1} and
          Native.shared_frame(buffer) == {2, 5, 0}
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 8192 in
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
        Native.shared_frame(buffer) == {1, 0, 3} and Native.shared_read(buffer) == {3, 2}
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law invalid_handle,
    expects:
      (try do
         Native.shared_frame(0)
         false
       rescue
         ArgumentError -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 1024)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law concurrent_frames,
    expects:
      (
        buffer = Native.shared_new()
        Native.shared_append(buffer, <<1, 0, 0, 1, 0, 0>>)
        parent = self()
        spawn(fn -> send(parent, {:parsed, Native.shared_frame(buffer)}) end)
        own = Native.shared_frame(buffer)

        receive do
          {:parsed, child} ->
            ((own == {2, 3, 3} and child == {2, 3, 0}) or
               (own == {2, 3, 0} and child == {2, 3, 3})) and
              Native.shared_read(buffer) == {0, 0}
        end
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 8192 in
    set_option cbv.maxSteps 2000000 in
    refine ⟨2, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    obtain ⟨depth, rfl⟩ := Nat.exists_eq_add_of_le' enough
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.check_sound (depth := 1024)
      (accept := fun outcome => outcome.isTrue) ?_ run terminal
    clear events last outcome run terminal
    cbv
    """
end
