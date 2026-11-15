defmodule LynxSharedBufferFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law empty,
    expects:
      LynxSharedBufferFixture.Native.shared_read(LynxSharedBufferFixture.Native.shared_new()) ==
        {0, 0},
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

  law appends,
    expects:
      (
        buffer = LynxSharedBufferFixture.Native.shared_new()
        first = LynxSharedBufferFixture.Native.shared_append(buffer, <<5, 9>>)
        second = LynxSharedBufferFixture.Native.shared_append(buffer, <<255>>)

        first == 2 and second == 3 and
          LynxSharedBufferFixture.Native.shared_read(buffer) == {3, 5}
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

  law alias_observes,
    expects:
      (
        buffer = LynxSharedBufferFixture.Native.shared_new()
        alias_handle = buffer
        LynxSharedBufferFixture.Native.shared_append(buffer, <<255, 128>>)
        LynxSharedBufferFixture.Native.shared_append(alias_handle, <<0>>)
        LynxSharedBufferFixture.Native.shared_read(buffer) == {3, 255}
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

  law rejected_input_preserves,
    expects:
      (
        buffer = LynxSharedBufferFixture.Native.shared_new()
        LynxSharedBufferFixture.Native.shared_append(buffer, <<7>>)

        rejected =
          try do
            LynxSharedBufferFixture.Native.shared_append(buffer, false)
            false
          rescue
            ArgumentError -> true
          end

        rejected and LynxSharedBufferFixture.Native.shared_read(buffer) == {1, 7}
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
         LynxSharedBufferFixture.Native.shared_read(0)
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

  law concurrent_appends,
    expects:
      (
        buffer = LynxSharedBufferFixture.Native.shared_new()
        parent = self()

        spawn(fn ->
          send(parent, {:appended, LynxSharedBufferFixture.Native.shared_append(buffer, <<2>>)})
        end)

        parent_length = LynxSharedBufferFixture.Native.shared_append(buffer, <<1>>)

        receive do
          {:appended, child_length} ->
            parent_length + child_length == 3 and
              case LynxSharedBufferFixture.Native.shared_read(buffer) do
                {2, head} -> head == 1 or head == 2
                _ -> false
              end
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
