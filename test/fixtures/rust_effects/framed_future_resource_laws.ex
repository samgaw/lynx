defmodule LynxEffectsFixture.FramedFutureCancelLaws do
  @compile :debug_info
  use Lynx.Laws

  law cancelled_future_preserves_value(amount),
    requires:
      is_integer(amount) and amount >= 0 and
        amount <= 18_446_744_073_709_551_615,
    expects:
      {LynxEffectsFixture.Native.counter_poll_cancel(:erlang.get(:counter), amount),
       LynxEffectsFixture.Native.counter_value(:erlang.get(:counter))} == {true, 7},
    proof: ~LEAN"""
    set_option maxRecDepth 8192 in
    cases amount <;> simp [«cancelled_future_preserves_value:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have bounds : 0 ≤ number ∧ number ≤ 18446744073709551615 := by
      simpa [«cancelled_future_preserves_value:requires/1»] using requires
    have nonnegative : 0 ≤ number := by omega
    let decoded : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 number.toNat⟩
    have decodedValue : decoded.val = number.toNat := by
      simp [decoded,Aeneas.Std.UScalar.val]
      omega
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have mutation := Shared.FramedFutureAdapter.owned_cancel_prefix (Lynx.Dispatcher.ofTable [] depth)
      7#u64 decoded 44 (by decide)
    have read := Shared.FramedTermAdapter.owned_read_prefix (Lynx.Dispatcher.ofTable [] depth)
      7#u64 45 (by decide)
    let finish := fun changed : Lynx.Term => do
      let handle ← Erlang.erlang.«get/1» (Lynx.Dispatcher.ofTable [] depth) (.atom "counter")
      let observed ← Elixir.LynxEffectsFixture.Native.«counter_value/1» (Lynx.Dispatcher.ofTable [] depth) handle
      Lynx.Result.ofExcept (Erlang.erlang.«==/2» (.tuple #[changed,observed])
        (.tuple #[Lynx.Term.true,.integer 7]))
    have tail : Lynx.Result.ReadyPrefix (finish Lynx.Term.true)
        (Shared.FramedTermAdapter.owned 7#u64 45) (.ok Lynx.Term.true)
        (Shared.FramedTermAdapter.owned 7#u64 47) := by
      simp only [finish,Erlang.erlang.«get/1»]
      apply Lynx.Result.ReadyPrefix.get
      simpa [Lynx.Result.bind,Lynx.Result.ok_bind,
        show Lynx.Rustler.encodeUnsigned (7#u64) = .integer 7 from rfl,
        Shared.FramedTermAdapter.owned,Shared.Properties.Framed.initialFor]
        using read.bind (fun observed => Lynx.Result.ofExcept
          (Erlang.erlang.«==/2» (.tuple #[Lynx.Term.true,observed])
            (.tuple #[Lynx.Term.true,.integer 7])))
    have returned : Lynx.Result.ReadyPrefix
        (Lynx.apply «cancelled_future_preserves_value:ensures/1» [] depth (.integer number))
        Shared.FramedTermAdapter.initial (.ok Lynx.Term.true)
        (Shared.FramedTermAdapter.owned 7#u64 47) := by
      simp only [Lynx.apply,«cancelled_future_preserves_value:ensures/1»,Erlang.erlang.«get/1»]
      apply Lynx.Result.ReadyPrefix.get
      have combined := (mutation.bind finish).trans (by simpa only [Lynx.Result.ok_bind] using tail)
      simpa [Lynx.Result.bind,Lynx.Result.ok_bind,finish,Erlang.erlang.«get/1»,Lynx.Rustler.encodeUnsigned,
        decodedValue,Int.toNat_of_nonneg nonnegative,Shared.FramedTermAdapter.initial,
        Shared.FramedTermAdapter.owned,Shared.Properties.Framed.initialFor] using combined
    exact returned.returns elapsed run terminal
    """
end
