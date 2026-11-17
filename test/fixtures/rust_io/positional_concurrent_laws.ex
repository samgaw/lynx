defmodule LynxPositionalFixture.Concurrent do
  @compile :debug_info
  use Lynx.Laws
  alias LynxPositionalFixture.Native

  law concurrent_patches,
    expects:
      (
        writer = :erlang.get(:writer)
        peer = :erlang.get(:peer)
        parent = self()

        spawn(fn ->
          send(parent, {:patched, Native.patch_at(peer, 0, 7)})
        end)

        wrote = Native.patch_at(writer, 0, 9)

        peer_wrote =
          receive do
            {:patched, result} -> result
          end

        observed = Native.observe_at(writer, 0)
        wrote and peer_wrote and (observed == 7 or observed == 9)
      ),
    proof: ~LEAN"""
    refine ⟨1, ?_⟩
    intro depth enough
    obtain ⟨remaining, rfl⟩ : ∃ remaining, depth = remaining + 1 := ⟨depth - 1, by omega⟩
    intro elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Positional.Concurrent.accepted_outcome
    apply Lynx.Concurrent.checkPost_sound (depth := 256) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
