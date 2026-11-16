defmodule LynxCapturedIoFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxCapturedIoFixture.Native

  law accepted,
    expects: Native.checked_write(<<7, 8>>, true) == {:ok, 2},
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

  law rejected,
    expects:
      (try do
         Native.checked_write(<<7, 8>>, false)
         false
       catch
         :error, :nif_panicked -> true
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

  law decoder_preserves_io,
    expects:
      (try do
         Native.checked_write(<<9>>, :invalid)
         false
       rescue
         ArgumentError -> Native.checked_write(<<7, 8>>, true) == {:ok, 2}
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

defmodule LynxCapturedIoFixture.ErrorLaws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxCapturedIoFixture.Native

  law opening_failure,
    expects: Native.checked_write(<<7, 8>>, false) == {:error, 2},
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
