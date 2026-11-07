defmodule LynxEffectsFixture.FileCreation do
  @compile :debug_info
  use Lynx.Laws

  law creates_resource,
    expects: is_reference(LynxFileResourceFixture.Native.file_create()),
    proof: ~LEAN"""
    simp only [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«creates_resource:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create:execution/0»,
      Lynx.Rustler.withResourceTypes,Lynx.Result.get_bind,Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply,Lynx.Result.set_continuation_apply,bind_assoc]
    rw [FileResource.Creation.create_env Lynx.Term.nil]
    all_goals simp [FileResource.Creation.seed,FileResource.Creation.initial,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName,
      Erlang.erlang.«is_reference/1»]
    """
end
