defmodule LynxEffectsFixture.FileCalls do
  @compile :debug_info
  use Lynx.Laws

  law release_then_sync,
    expects:
      (
        resource = :erlang.get(:file)

        LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    let computation := Lynx.apply «release_then_sync:ensures/0» []
    obtain ⟨_, _, run, final⟩ := Lynx.Result.run_reaches computation FileResource.Calls.seed schedule
    have checked : Lynx.Concurrent.check
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 128
        (.start FileResource.Calls.seed computation) = true := by
      set_option maxHeartbeats 4000000 in
      set_option maxRecDepth 4096 in
      set_option cbv.maxSteps 2000000 in cbv
    have accepted := Lynx.Concurrent.check_sound checked run final
    rw [← Lynx.concurrentFrom_eq_run] at accepted
    split at accepted
    · assumption
    · contradiction
    """

  law sync_release_sync,
    expects:
      (
        resource = :erlang.get(:file)

        LynxFileResourceFixture.Native.file_sync(resource) and
          LynxFileResourceFixture.Native.file_release(resource) == {} and
          LynxFileResourceFixture.Native.file_sync(resource)
      ),
    proof: ~LEAN"""
    let computation := Lynx.apply «sync_release_sync:ensures/0» []
    obtain ⟨_, _, run, final⟩ := Lynx.Result.run_reaches computation FileResource.Calls.seed schedule
    have checked : Lynx.Concurrent.check
        (fun | .ok (Lynx.Term.atom "true") => true | _ => false) 128
        (.start FileResource.Calls.seed computation) = true := by
      set_option maxHeartbeats 4000000 in
      set_option maxRecDepth 4096 in
      set_option cbv.maxSteps 2000000 in cbv
    have accepted := Lynx.Concurrent.check_sound checked run final
    rw [← Lynx.concurrentFrom_eq_run] at accepted
    split at accepted
    · assumption
    · contradiction
    """

  law rejects_integer_sync(input),
    requires: is_integer(input),
    expects:
      (try do
         LynxFileResourceFixture.Native.file_sync(input)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    cases input <;> simp_all [«rejects_integer_sync:requires/1», Erlang.erlang.«is_integer/1»]
    simp only [Lynx.concurrentFrom_eq_run,Lynx.apply_eq,«rejects_integer_sync:ensures/1»,
      Elixir.LynxFileResourceFixture.Native.«file_sync/1»,Lynx.Rustler.withResourceTypes,
      Lynx.Result.tryWith_eq, Lynx.Result.handle_nativeGet, Lynx.Result.handle_nativeSet,
      Lynx.Result.handle_nativeModify, Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run,
      Lynx.Result.nativeGet_bind, Lynx.Result.nativeSet_bind,
      Lynx.Result.nativeGet_continuation_run, Lynx.Result.nativeSet_continuation_run,Lynx.Result.handle_get,Lynx.Result.handle_set,
      Lynx.Result.get_bind,Lynx.Result.set_bind,Lynx.Result.get_continuation_apply,
      Lynx.Result.set_continuation_apply,bind_assoc]
    rw [Lynx.NativeResourceArc.decode_nonreference_handled_next _ (by intro identity; simp)]
    simp [Lynx.Result.ok_bind,Lynx.Result.ok_apply,Lynx.Exception.classTerm,Lynx.Exception.reason]
    """
end
