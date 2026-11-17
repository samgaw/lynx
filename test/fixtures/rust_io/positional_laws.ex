defmodule LynxPositionalFixture.Success do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law patch_and_observe,
    expects:
      (
        file = :erlang.get(:slots)

        Native.patch_at(file, 4, 9) and Native.observe_at(file, 4) == 9 and
          is_nil(Native.observe_at(file, 5)) and Native.observe_at(file, 0) == 1
      ),
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Positional.Nif.accepted Positional.Nif.patched .nil 4) 256
        (.start Positional.Nif.ready
          (Lynx.apply «patch_and_observe:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    exact terminal.outcome_eq.symm.trans
      (Positional.Nif.accepted_outcome (Lynx.Concurrent.checkPost_sound verified run terminal))
    """
end

defmodule LynxPositionalFixture.Short do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law zero_write_is_unacknowledged,
    expects:
      (
        file = :erlang.get(:slots)
        Native.patch_at(file, 4, 9) == false and Native.observe_at(file, 0) == 1
      ),
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Positional.Nif.accepted Positional.Nif.original .nil 2) 256
        (.start Positional.Nif.short
          (Lynx.apply «zero_write_is_unacknowledged:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    exact terminal.outcome_eq.symm.trans
      (Positional.Nif.accepted_outcome (Lynx.Concurrent.checkPost_sound verified run terminal))
    """
end

defmodule LynxPositionalFixture.Invalid do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law rejects_negative_offset,
    expects:
      (try do
         Native.patch_at(:erlang.get(:slots), -1, 9)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    -- Decoding the resource acquires one owner, which the adapter releases on badarg.
    have verified : Lynx.Concurrent.checkPost
        (Positional.Nif.accepted Positional.Nif.original Positional.Nif.successScript 1) 256
        (.start Positional.Nif.ready
          (Lynx.apply «rejects_negative_offset:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    exact terminal.outcome_eq.symm.trans
      (Positional.Nif.accepted_outcome (Lynx.Concurrent.checkPost_sound verified run terminal))
    """
end
