defmodule LynxRwResourceFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law initial_value,
    expects:
      LynxRwResourceFixture.Native.shared_read(LynxRwResourceFixture.Native.shared_new(true)) ==
        true,
    proof: ~LEAN"""
    set_option maxRecDepth 2048 in
      simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «initial_value:ensures/0»]
      rw [Elixir.LynxRwResourceFixture.Native.«shared_new/1»]
      unfold Lynx.Rustler.withResourceTypes
      rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
      unfold Elixir.LynxRwResourceFixture.Native.«shared_new:execution/1»
      rw [show Lynx.Result.ofExcept (Lynx.Rustler.decodeBool (.atom "true")) =
        Lynx.Result.ok true from rfl]
      rw [Lynx.Result.ok_bind]
      change (Lynx.Result.run _ RwShared.Properties.initial schedule).1 = _
      rw [RwShared.Properties.factory_next true _ schedule]
      unfold Elixir.LynxRwResourceFixture.Native.«shared_read/1»
        Elixir.LynxRwResourceFixture.Native.«shared_read:execution/1»
        Lynx.Rustler.withResourceTypes
      rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
      change (Lynx.Result.run _ (RwShared.Properties.pinned true 5) schedule).1 = _
      simp only [bind_assoc]
      rw [RwShared.Properties.read_next true 5 (by decide) _ schedule]
      simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law shared_write,
    expects:
      (
        resource = LynxRwResourceFixture.Native.shared_new(false)

        LynxRwResourceFixture.Native.shared_toggle(resource) == true and
          LynxRwResourceFixture.Native.shared_read(resource) == true
      ),
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «shared_write:ensures/0»]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_new/1»
      Elixir.LynxRwResourceFixture.Native.«shared_new:execution/1»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    rw [show Lynx.Result.ofExcept (Lynx.Rustler.decodeBool (.atom "false")) =
      Lynx.Result.ok false from rfl, Lynx.Result.ok_bind]
    change (Lynx.Result.run _ RwShared.Properties.initial schedule).1 = _
    rw [RwShared.Properties.factory_next false _ schedule]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_toggle/1»
      Elixir.LynxRwResourceFixture.Native.«shared_toggle:execution/1»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    change (Lynx.Result.run _ (RwShared.Properties.pinned false 5) schedule).1 = _
    simp only [bind_assoc]
    rw [RwShared.Properties.toggle_next false 5 (by decide) _ schedule]
    simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2», Lynx.Result.andAlso,
      Lynx.Result.bind]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_read/1»
      Elixir.LynxRwResourceFixture.Native.«shared_read:execution/1»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    change (Lynx.Result.run _ (RwShared.Properties.pinned true 9) schedule).1 = _
    simp only [bind_assoc]
    rw [RwShared.Properties.read_next true 9 (by decide) _ schedule]
    simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law two_writes,
    expects:
      (
        resource = LynxRwResourceFixture.Native.shared_new(true)
        LynxRwResourceFixture.Native.shared_toggle(resource)
        LynxRwResourceFixture.Native.shared_toggle(resource)
        LynxRwResourceFixture.Native.shared_read(resource) == true
      ),
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «two_writes:ensures/0»]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_new/1»
      Elixir.LynxRwResourceFixture.Native.«shared_new:execution/1»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    rw [show Lynx.Result.ofExcept (Lynx.Rustler.decodeBool (.atom "true")) =
      Lynx.Result.ok true from rfl, Lynx.Result.ok_bind]
    change (Lynx.Result.run _ RwShared.Properties.initial schedule).1 = _
    rw [RwShared.Properties.factory_next true _ schedule]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_toggle/1»
      Elixir.LynxRwResourceFixture.Native.«shared_toggle:execution/1»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    change (Lynx.Result.run _ (RwShared.Properties.pinned true 5) schedule).1 = _
    simp only [bind_assoc]
    rw [RwShared.Properties.toggle_next true 5 (by decide) _ schedule]
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    change (Lynx.Result.run _ (RwShared.Properties.pinned false 9) schedule).1 = _
    simp only [bind_assoc]
    rw [RwShared.Properties.toggle_next false 9 (by decide) _ schedule]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_read/1»
      Elixir.LynxRwResourceFixture.Native.«shared_read:execution/1»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    change (Lynx.Result.run _ (RwShared.Properties.pinned true 13) schedule).1 = _
    simp only [bind_assoc]
    rw [RwShared.Properties.read_next true 13 (by decide) _ schedule]
    simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law accepted_request,
    expects: LynxRwResourceFixture.Native.shared_checked(false, true) == true,
    proof: ~LEAN"""
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «accepted_request:ensures/0»]
    unfold Elixir.LynxRwResourceFixture.Native.«shared_checked/2»
      Elixir.LynxRwResourceFixture.Native.«shared_checked:execution/2»
      Lynx.Rustler.withResourceTypes
    rw [Lynx.Result.nativeModify_bind, Lynx.Result.nativeModify_run _ _ _ schedule]
    rw [show Lynx.Result.ofExcept (Lynx.Rustler.decodeBool (.atom "false")) =
      Lynx.Result.ok false from rfl, Lynx.Result.ok_bind]
    rw [show Lynx.Result.ofExcept (Lynx.Rustler.decodeBool (.atom "true")) =
      Lynx.Result.ok true from rfl, Lynx.Result.ok_bind]
    change (Lynx.Result.run _ RwShared.Properties.initial schedule).1 = _
    rw [RwShared.Properties.checked_next false true _ schedule]
    simp [Lynx.Rustler.encodeBool, Erlang.erlang.«==/2»]
    """

  law invalid_resource,
    expects:
      (try do
         LynxRwResourceFixture.Native.shared_read(7)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    simp [Lynx.concurrent_eq_run, «invalid_resource:ensures/0»,
      Elixir.LynxRwResourceFixture.Native.«shared_read/1», Lynx.Rustler.withResourceTypes,
      Lynx.NativeResourceArc.decode_eq, Lynx.Result.tryWith, Lynx.Result.handle,
      Lynx.Result.bind, Lynx.Exception.classTerm, Lynx.Exception.reason,
      List.eraseDups_cons, List.eraseDups_nil]
    """
end
