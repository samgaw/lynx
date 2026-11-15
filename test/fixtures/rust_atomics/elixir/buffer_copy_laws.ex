defmodule LynxVectorBufferFixture.CopyLaws do
  @compile :debug_info
  use Lynx.Laws

  law copies,
    expects:
      (
        buffer = LynxVectorBufferFixture.Native.buffer_copy(<<5, 9, 255>>)

        LynxVectorBufferFixture.Native.buffer_length(buffer) == 3 and
          LynxVectorBufferFixture.Native.buffer_head(buffer) == 5
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 32768 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 768)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law empty,
    expects:
      (
        buffer = LynxVectorBufferFixture.Native.buffer_copy(<<>>)

        LynxVectorBufferFixture.Native.buffer_length(buffer) == 0 and
          LynxVectorBufferFixture.Native.buffer_head(buffer) == 0
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 32768 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 768)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law raw_bytes,
    expects:
      (
        buffer = LynxVectorBufferFixture.Native.buffer_copy(<<255, 128, 0>>)

        LynxVectorBufferFixture.Native.buffer_length(buffer) == 3 and
          LynxVectorBufferFixture.Native.buffer_head(buffer) == 255
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 32768 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 768)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law independent_buffers,
    expects:
      (
        first = LynxVectorBufferFixture.Native.buffer_copy(<<1, 2>>)
        second = LynxVectorBufferFixture.Native.buffer_copy(<<9>>)

        LynxVectorBufferFixture.Native.buffer_head(first) == 1 and
          LynxVectorBufferFixture.Native.buffer_length(first) == 2 and
          LynxVectorBufferFixture.Native.buffer_head(second) == 9
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 32768 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 768)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law rejects_list,
    expects:
      (try do
         LynxVectorBufferFixture.Native.buffer_copy([1, 2])
         false
       rescue
         ArgumentError -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 32768 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 768)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law rejects_bits,
    expects:
      (try do
         LynxVectorBufferFixture.Native.buffer_copy(<<1::1>>)
         false
       rescue
         ArgumentError -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 24000000 in
    set_option maxRecDepth 32768 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 768)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end
