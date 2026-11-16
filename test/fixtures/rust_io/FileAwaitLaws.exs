defmodule LynxFileAwaitFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxFileAwaitFixture.Native

  law accepted,
    expects: Native.write_poll(7, 8, true) == {:ok, 2},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 512)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law cancelled,
    expects: Native.write_poll(7, 8, false) == {:ok, nil},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 512)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law narrowed,
    expects: Native.write_poll(263, 264, false) == {:ok, nil},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 512)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law decoder_preserves_io,
    expects:
      (try do
         Native.write_poll(4_294_967_296, 8, false)
         false
       rescue
         ArgumentError -> Native.write_poll(7, 8, false) == {:ok, nil}
       end),
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 512)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end

defmodule LynxFileAwaitFixture.ErrorLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxFileAwaitFixture.Native

  law opening_failure,
    expects: Native.write_poll(7, 8, false) == {:error, 2},
    proof: ~LEAN"""
    set_option maxRecDepth 16384 in
    set_option maxHeartbeats 12000000 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 512)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end
