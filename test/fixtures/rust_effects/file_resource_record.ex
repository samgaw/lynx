defmodule LynxEffectsFixture.CheckedFileCommits do
  @compile :debug_info
  use Lynx.Laws

  law record_then_commit(input),
    requires: is_integer(input) and input >= 0 and input < 4_294_967_296,
    expects:
      (
        resource = LynxFileResourceFixture.Native.file_create()

        LynxFileResourceFixture.Native.file_write_record(resource, input) and
          LynxFileResourceFixture.Native.file_commit(resource)
      ),
    proof: ~LEAN"""
    cases input <;> simp [«record_then_commit:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    have actual_adapter (dispatcher : Lynx.Dispatcher) :
        Elixir.LynxFileResourceFixture.Native.«file_commit/1» dispatcher (.reference 6) =
          FileResource.CallPrefix.registered_invoke := by rfl
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«record_then_commit:ensures/1»,
      Elixir.LynxFileResourceFixture.Native.«file_create/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create:execution/0»,
      Elixir.LynxFileResourceFixture.Native.«file_write_record/2»,
      Elixir.LynxFileResourceFixture.Native.«file_write_record:execution/2»,
      Lynx.Rustler.withResourceTypes,Lynx.Rustler.decodeUnsigned,range.1,range.2,Lynx.Result.ofExcept,
      Lynx.Result.handle,FileResource.Record.recordSeed]
    let value : Aeneas.Std.U16 := ⟨BitVec.ofNat 16 number.toNat⟩
    rw [FileResource.Creation.create_env (rest := FileResource.Publish.opening) FileResource.Record.before.script]
    all_goals simp [FileResource.Creation.initial,FileResource.Record.returned_before,
      FileResource.CreatedCalls.pinnedEnv,Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Record.write_env (ns := FileResource.Publish.namespaceBefore) FileResource.Record.before (FileResource.Record.written value)
      FileResource.Record.before_valid FileResource.Record.before_ready value 4#usize
      (FileResource.Record.full_step value)]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,Lynx.Rustler.encodeBool,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [actual_adapter]
    simp [FileResource.CallPrefix.registered_invoke,Lynx.Rustler.withResourceTypes,FileResource.CallPrefix.invoke]
    rw [FileResource.CallPrefix.call_run value]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """
end
