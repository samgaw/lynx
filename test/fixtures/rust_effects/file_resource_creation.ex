defmodule LynxEffectsFixture.FileCreation do
  @compile :debug_info
  use Lynx.Laws

  law creates_resource,
    expects: is_reference(LynxFileResourceFixture.Native.file_create()),
    proof: ~LEAN"""
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply FileResource.Creation.accepted_outcome last
    apply Lynx.Concurrent.checkPost_sound (depth := 32) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end
