defmodule LynxEffectsFixture.FileCommits do
  @compile :debug_info
  use Lynx.Laws

  law write_then_commit(input),
    requires: is_integer(input) and input >= 0 and input < 4_294_967_296,
    expects:
      (
        resource = LynxFileResourceFixture.Native.file_create()

        LynxFileResourceFixture.Native.file_write(resource, input) and
          LynxFileResourceFixture.Native.file_commit(resource)
      ),
    proof: ~LEAN"""
    cases input <;> simp [«write_then_commit:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«write_then_commit:ensures/1»,
      Elixir.LynxFileResourceFixture.Native.«file_create/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create:execution/0»,
      Elixir.LynxFileResourceFixture.Native.«file_write/2»,
      Elixir.LynxFileResourceFixture.Native.«file_write:execution/2»,
      Elixir.LynxFileResourceFixture.Native.«file_commit/1»,
      Elixir.LynxFileResourceFixture.Native.«file_commit:execution/1»,
      Lynx.Rustler.withResourceTypes,Lynx.Rustler.decodeUnsigned,range.1,range.2,Lynx.Result.ofExcept,
      Lynx.Result.handle,FileResource.Publish.seed]
    let value : Aeneas.Std.U16 := ⟨BitVec.ofNat 16 number.toNat⟩
    rw [FileResource.Creation.create_env (rest := FileResource.Publish.opening) FileResource.Write.before.script]
    all_goals simp [FileResource.Creation.initial,FileResource.Publish.returned_before,
      FileResource.CreatedCalls.pinnedEnv,Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Write.write_env (ns := FileResource.Publish.namespaceBefore) FileResource.Write.before (FileResource.Write.written value)
      FileResource.Write.before_valid FileResource.Write.before_ready value 2#usize
      (FileResource.Write.full_step value)]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,Lynx.Rustler.encodeBool,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Publish.commit_run value]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """
end
