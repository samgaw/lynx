defmodule LynxEffectsFixture.FailedDirectoryCommits do
  @compile :debug_info
  use Lynx.Laws

  law directory_failure_not_acknowledged,
    expects: not LynxFileResourceFixture.Native.file_commit(:erlang.get(:resource)),
    proof: ~LEAN"""
    simp [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«directory_failure_not_acknowledged:ensures/0»,
      Elixir.LynxFileResourceFixture.Native.«file_commit/1»,
      Elixir.LynxFileResourceFixture.Native.«file_commit:execution/1»,
      Lynx.Rustler.withResourceTypes,Erlang.erlang.«get/1»,Lynx.Result.monadGet_eq,
      Lynx.Environment.pdict,Lynx.Environment.setPdict,
      FileResource.DirectoryFailure.seed,
      FileResource.DirectoryFailure.initial]
    let value : Aeneas.Std.U16 := 4660#u16
    rw [FileResource.DirectoryFailure.failure_env value]
    case heap => rfl
    all_goals first | rfl | simp [Lynx.NativeResourceArc.typeName,Lynx.NativeCodec.typeName,
      Erlang.erlang.«not/1»,Lynx.Result.ofExcept]
    """
end
