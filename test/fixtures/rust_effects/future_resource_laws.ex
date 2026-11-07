defmodule LynxEffectsFixture.FutureCancelLaws do
  @compile :debug_info
  use Lynx.Laws

  law cancelled_without_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        LynxEffectsFixture.Native.counter_poll_cancel(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 7
      ),
    proof: ~LEAN"""
    let seven : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 7⟩
    let three : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 3⟩
    have input : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 7) = .ok seven := rfl
    have amount : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 3) = .ok three := rfl
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «cancelled_without_update:ensures/0»,
      Elixir.LynxEffectsFixture.Native.«counter_new/1»,
      Elixir.LynxEffectsFixture.Native.«counter_new:execution/1»,
      Elixir.LynxEffectsFixture.Native.«counter_poll_cancel/2»,
      Elixir.LynxEffectsFixture.Native.«counter_poll_cancel:execution/2»,
      Elixir.LynxEffectsFixture.Native.«counter_value/1»,
      Elixir.LynxEffectsFixture.Native.«counter_value:execution/1»,
      Lynx.Rustler.withResourceTypes, input, amount, Lynx.Result.ofExcept,
      Lynx.Result.ok_bind, Lynx.Result.handle, Lynx.Result.andAlso_eq, Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.Properties.create_next seven _ _ (by simp [Lynx.NativeResourceArc.typeName]) rfl rfl]
    simp only [Lynx.Result.get_bind, Lynx.Result.set_bind, Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.PollProperties.cancel_call_at _ seven three 5 (by decide) _ rfl rfl
      (by simp [Lynx.NativeResourceArc.typeName])]
    simp only [Lynx.Result.andAlso_eq, Lynx.Result.ok_bind, Lynx.Term.true,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply]
    rw [Shared.Properties.read_call_at _ seven 6 (by decide) _ rfl rfl (by simp [Lynx.NativeResourceArc.typeName])]
    simp [seven, Aeneas.Std.UScalar.val, Erlang.erlang.«==/2»,
      -Aeneas.Std.UScalar.bv_toNat]
    """
end
