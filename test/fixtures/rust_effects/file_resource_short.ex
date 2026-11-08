defmodule LynxEffectsFixture.ShortFileCommits do
  @compile :debug_info
  use Lynx.Laws

  law short_record_not_committed(input),
    requires: is_integer(input) and input >= 0 and input < 4_294_967_296,
    expects:
      (
        resource = LynxFileResourceFixture.Native.file_create()

        not (LynxFileResourceFixture.Native.file_write_record(resource, input) and
               LynxFileResourceFixture.Native.file_commit(resource))
      ),
    proof: ~LEAN"""
    cases input <;> simp [«short_record_not_committed:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«short_record_not_committed:ensures/1»,
      Elixir.LynxFileResourceFixture.Native.«file_create/0»,
      Elixir.LynxFileResourceFixture.Native.«file_create:execution/0»,
      Elixir.LynxFileResourceFixture.Native.«file_write_record/2»,
      Elixir.LynxFileResourceFixture.Native.«file_write_record:execution/2»,
      Elixir.LynxFileResourceFixture.Native.«file_commit/1»,
      Elixir.LynxFileResourceFixture.Native.«file_commit:execution/1»,
      Lynx.Rustler.withResourceTypes,Lynx.Rustler.decodeUnsigned,range.1,range.2,Lynx.Result.ofExcept,
      Lynx.Result.handle,FileResource.ShortRecovery.seed]
    let value : Aeneas.Std.U16 := ⟨BitVec.ofNat 16 number.toNat⟩
    have short : 3 < 4 := by decide +kernel
    have flag := FileResource.ShortRecovery.short_flag 3 short
    rw [FileResource.Creation.create_env (rest := .nil) (FileResource.ShortRecovery.partialBefore 3).script]
    all_goals simp [FileResource.Creation.initial,FileResource.ShortRecovery.returned_before,
      FileResource.CreatedCalls.pinnedEnv,Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    rw [FileResource.Record.write_env (ns := FileResource.CreatedCalls.pendingNamespace)
      (FileResource.ShortRecovery.partialBefore 3) (FileResource.ShortRecovery.partialState value 3)
      (FileResource.ShortRecovery.partial_valid 3) rfl value (FileResource.ShortRecovery.writtenCount 3 short)
      (FileResource.ShortRecovery.partial_step value 3 short)]
    all_goals simp [FileResource.CreatedCalls.pinnedEnv,flag,
      Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName]
    """
end
