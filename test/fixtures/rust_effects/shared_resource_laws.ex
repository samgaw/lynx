defmodule LynxEffectsFixture.SharedLaws do
  @compile :debug_info
  use Lynx.Laws

  law shared_update,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        LynxEffectsFixture.Native.counter_add(resource, 3) and
          LynxEffectsFixture.Native.counter_value(resource) == 10
      ),
    proof: ~LEAN"""
    let seven : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 7⟩
    let three : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 3⟩
    let ten : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 10⟩
    have input : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 7) = .ok seven := rfl
    have amount : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 3) = .ok three := rfl
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «shared_update:ensures/0»,
      Elixir.LynxEffectsFixture.Native.«counter_new/1»,
      Elixir.LynxEffectsFixture.Native.«counter_new:execution/1»,
      Elixir.LynxEffectsFixture.Native.«counter_add/2»,
      Elixir.LynxEffectsFixture.Native.«counter_add:execution/2»,
      Elixir.LynxEffectsFixture.Native.«counter_value/1»,
      Elixir.LynxEffectsFixture.Native.«counter_value:execution/1»,
      Lynx.Rustler.withResourceTypes, input, amount, Lynx.Result.ofExcept,
      Lynx.Result.ok_bind, Lynx.Result.handle, Lynx.Result.andAlso_eq, Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.Properties.create_next seven _ _ (by simp [Lynx.NativeResourceArc.typeName]) rfl rfl]
    simp only [Lynx.Result.get_bind, Lynx.Result.set_bind, Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.Properties.add_safe_call_at _ seven three ten 5 (by decide) _ rfl rfl
      (by simp [Lynx.NativeResourceArc.typeName])
      (by simp [seven, three, Aeneas.Std.UScalar.val, Aeneas.Std.U64.max, Aeneas.Std.U64.numBits])
      (by simp [seven, three, ten, Aeneas.Std.UScalar.val])]
    simp only [Lynx.Result.andAlso_eq, Lynx.Result.ok_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply]
    rw [Shared.Properties.read_call_at _ ten 7 (by decide) _ rfl rfl (by simp [Lynx.NativeResourceArc.typeName])]
    simp [seven, three, ten, Aeneas.Std.UScalar.val, Erlang.erlang.«==/2»,
      -Aeneas.Std.UScalar.bv_toNat]
    """

  law overflow_preserves,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(18_446_744_073_709_551_615)

        LynxEffectsFixture.Native.counter_add(resource, 1) == false and
          LynxEffectsFixture.Native.counter_value(resource) == 18_446_744_073_709_551_615
      ),
    proof: ~LEAN"""
    let largest : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 18446744073709551615⟩
    let one : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 1⟩
    have input : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 18446744073709551615) = .ok largest := rfl
    have amount : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 1) = .ok one := rfl
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «overflow_preserves:ensures/0»,
      Elixir.LynxEffectsFixture.Native.«counter_new/1»,
      Elixir.LynxEffectsFixture.Native.«counter_new:execution/1»,
      Elixir.LynxEffectsFixture.Native.«counter_add/2»,
      Elixir.LynxEffectsFixture.Native.«counter_add:execution/2»,
      Elixir.LynxEffectsFixture.Native.«counter_value/1»,
      Elixir.LynxEffectsFixture.Native.«counter_value:execution/1»,
      Lynx.Rustler.withResourceTypes, input, amount, Lynx.Result.ofExcept,
      Lynx.Result.ok_bind, Lynx.Result.handle, Lynx.Result.andAlso_eq, Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.Properties.create_next largest _ _ (by simp [Lynx.NativeResourceArc.typeName]) rfl rfl]
    simp only [Lynx.Result.get_bind, Lynx.Result.set_bind, Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.Properties.add_overflow_call_at _ largest one 5 (by decide) _ rfl rfl
      (by simp [Lynx.NativeResourceArc.typeName])
      (by simp [largest, one, Aeneas.Std.UScalar.val, Aeneas.Std.U64.max, Aeneas.Std.U64.numBits])]

    simp only [Lynx.Result.andAlso_eq, Lynx.Result.ok_bind, Lynx.Result.ofExcept, Erlang.erlang.«==/2», Lynx.Term.compare_self, ↓reduceIte, Lynx.Term.true,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply]
    rw [Shared.Properties.read_call_at _ largest 7 (by decide) _ rfl rfl (by simp [Lynx.NativeResourceArc.typeName])]
    simp [largest, one, largest, Aeneas.Std.UScalar.val, Erlang.erlang.«==/2»,
      -Aeneas.Std.UScalar.bv_toNat]
    """

  law decoder_cleanup,
    expects:
      (
        resource = LynxEffectsFixture.Native.counter_new(7)

        caught =
          try do
            LynxEffectsFixture.Native.counter_add(resource, false)
            false
          catch
            :error, :badarg -> true
          end

        caught and LynxEffectsFixture.Native.counter_value(resource) == 7
      ),
    proof: ~LEAN"""
    let seven : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 7⟩
    have input : Lynx.Rustler.decodeUnsigned .U64 64 (.integer 7) = .ok seven := rfl
    simp only [Lynx.concurrent_eq_run, Lynx.apply_eq, «decoder_cleanup:ensures/0»,
      Elixir.LynxEffectsFixture.Native.«counter_new/1»,
      Elixir.LynxEffectsFixture.Native.«counter_new:execution/1»,
      Elixir.LynxEffectsFixture.Native.«counter_add/2»,
      Elixir.LynxEffectsFixture.Native.«counter_add:execution/2»,
      Elixir.LynxEffectsFixture.Native.«counter_value/1»,
      Elixir.LynxEffectsFixture.Native.«counter_value:execution/1»,
      Lynx.Rustler.withResourceTypes, input, Lynx.Result.ofExcept,
      Lynx.Result.ok_bind, Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    rw [Shared.Properties.create_next seven _ _ (by simp [Lynx.NativeResourceArc.typeName]) rfl rfl]
    simp only [Lynx.Result.andAlso_eq, Lynx.Result.tryWith_eq,
      Lynx.Result.handle_get, Lynx.Result.handle_set, Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply, bind_assoc]
    simp only [Lynx.Rustler.decodeUnsigned, Lynx.Result.ofExcept, Lynx.Result.handle_error,
      bind_assoc, Lynx.Result.error_bind]
    rw [Shared.Properties.decoder_badarg_cleanup_at _ seven 5 (by decide) _ _ rfl rfl
      (by simp [Lynx.NativeResourceArc.typeName])]
    simp only [Lynx.Exception.classTerm, Lynx.Exception.reason, Lynx.Result.pure_eq_ok, Lynx.Result.ok_bind,
      Lynx.Result.get_bind, Lynx.Result.set_bind,
      Lynx.Result.get_continuation_apply, Lynx.Result.set_continuation_apply]
    rw [Shared.Properties.read_call_at _ seven 6 (by decide) _ rfl rfl
      (by simp [Lynx.NativeResourceArc.typeName])]
    simp [seven, Aeneas.Std.UScalar.val, Erlang.erlang.«==/2», -Aeneas.Std.UScalar.bv_toNat]
    """
end
