defmodule LynxIoFixture.SharedLogLaws do
  @compile :debug_info
  use Lynx.Laws

  law append_existing(value),
    requires: is_integer(value) and value >= 0 and value < 4_294_967_296,
    expects: LynxIoFixture.Native.log_append(:erlang.get(:log), value) == true,
    proof: ~LEAN"""
    set_option maxRecDepth 4096 in
      cases value <;> simp [«append_existing:requires/1», Erlang.erlang.«is_integer/1»] at requires
      rename_i number
      have range : (0 : Int) ≤ number ∧ number < 4294967296 := by omega
      have upper : number < (2 : Int) ^ 32 := range.2
      refine ⟨0, ?_⟩
      intro depth _
      apply Lynx.concurrentFrom_of_readyPrefix
      simp only [Lynx.apply_eq, «append_existing:ensures/1»,
        Erlang.erlang.«get/1», Lynx.Result.monadGet_eq, Lynx.Result.get_bind]
      apply Lynx.Result.ReadyPrefix.get
      simp only [Record.NativeLogProperties.initial, Record.NativeLogProperties.pinned,
        Record.FramedLogProperties.framedEnv, Lynx.Result.ok_bind,
        Elixir.LynxIoFixture.Native.«log_append/2»,
        Elixir.LynxIoFixture.Native.«log_append:execution/2»,
        Lynx.Rustler.decodeUnsigned, range.1, upper, and_self, ite_true,
        Lynx.Result.ofExcept, Lynx.Result.handle, Lynx.Rustler.withResourceTypes, Lynx.Result.nativeModify_bind]
      apply Lynx.Result.ReadyPrefix.nativeModify
      · rfl
      exact (Record.NativeLogProperties.initial_prefix
        (⟨BitVec.ofNat _ number.toNat⟩ : Aeneas.Std.U16)
        {Record.NativeLogProperties.initial with nativeResourceTypes :=
          (Record.NativeLogProperties.initial.nativeResourceTypes ++
            [Lynx.NativeResourceArc.typeName io_native.shared_log.LogResource]).eraseDups}
        rfl rfl (by simp [List.mem_eraseDups])).bind
        (fun result => Lynx.Result.ofExcept (Erlang.erlang.«==/2» result Lynx.Term.true))
    """
end
