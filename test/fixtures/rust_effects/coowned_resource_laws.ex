defmodule LynxEffectsFixture.CoownedResourceLaws do
  @compile :debug_info
  use Lynx.Laws

  law shared_owners_survive,
    expects: LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), 3),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Shared.FramedTermAdapter.accepted 10#u64 46) 256
        (.start Shared.FramedTermAdapter.initial
          (Lynx.apply «shared_owners_survive:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.FramedTermAdapter.accepted_outcome 10#u64 46 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """

  law overflow_keeps_owners,
    expects:
      LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), 18_446_744_073_709_551_615) ==
        false,
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Shared.FramedTermAdapter.accepted 7#u64 46) 256
        (.start Shared.FramedTermAdapter.initial
          (Lynx.apply «overflow_keeps_owners:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.FramedTermAdapter.accepted_outcome 7#u64 46 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """

  law badarg_keeps_owners,
    expects:
      (try do
         LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have verified : Lynx.Concurrent.checkPost
        (Shared.FramedTermAdapter.accepted 7#u64 45) 256
        (.start Shared.FramedTermAdapter.initial
          (Lynx.apply «badarg_keeps_owners:ensures/0» [] depth) elapsed) = true := by
      clear enough events last outcome run terminal
      lynx_check_post
    have accepted := Shared.FramedTermAdapter.accepted_outcome 7#u64 45 last
      (Lynx.Concurrent.checkPost_sound verified run terminal)
    exact terminal.outcome_eq.symm.trans accepted
    """

  law bounded_add_succeeds(amount),
    requires: is_integer(amount) and amount >= 0 and amount <= 18_446_744_073_709_551_608,
    expects: LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), amount),
    proof: ~LEAN"""
    set_option maxRecDepth 8192 in
    cases amount <;> simp [«bounded_add_succeeds:requires/1», Erlang.erlang.«is_integer/1»] at requires
    rename_i number
    have bounds : 0 ≤ number ∧ number ≤ 18446744073709551608 := by
      simpa [«bounded_add_succeeds:requires/1»] using requires
    let decoded : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 number.toNat⟩
    have width : number.toNat < 2^64 := by omega
    have decodedValue : decoded.val = number.toNat := by
      simp [decoded,Aeneas.Std.UScalar.val]
      omega
    have fits : (7#u64).val + decoded.val ≤ Aeneas.Std.U64.max := by
      rw [decodedValue]
      scalar_tac
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    obtain ⟨updated,trace,sum⟩ := Shared.FramedTermAdapter.owned_add_success
      (Lynx.Dispatcher.ofTable [] depth) 7#u64 decoded 44 (by decide) fits
    have returned : Lynx.Result.ReadyPrefix
        (Lynx.apply «bounded_add_succeeds:ensures/1» [] depth (.integer number))
        Shared.FramedTermAdapter.initial (.ok Lynx.Term.true)
        (Shared.FramedTermAdapter.owned updated 46) := by
      simp only [Lynx.apply, «bounded_add_succeeds:ensures/1», Erlang.erlang.«get/1»,
        Lynx.Result.get_bind, Lynx.Result.ok_bind]
      apply Lynx.Result.ReadyPrefix.get
      simpa [Lynx.Result.bind,Lynx.Result.ok_bind,Lynx.Rustler.encodeUnsigned,decodedValue,Int.toNat_of_nonneg bounds.1,
        Shared.FramedTermAdapter.initial,Shared.FramedTermAdapter.owned,
        Shared.Properties.Framed.initialFor] using trace
    exact returned.returns elapsed run terminal
    """

  law bounded_adds_compose(left, right),
    requires:
      is_integer(left) and is_integer(right) and left >= 0 and right >= 0 and
        left + right <= 18_446_744_073_709_551_608,
    expects:
      {LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), left),
       LynxEffectsFixture.Native.counter_add(:erlang.get(:counter), right)} == {true, true},
    proof: ~LEAN"""
    set_option maxRecDepth 8192 in
    cases left <;> simp [«bounded_adds_compose:requires/2», Erlang.erlang.«is_integer/1»] at requires
    rename_i leftNumber
    cases right <;> simp at requires
    rename_i rightNumber
    have bounds : 0 ≤ leftNumber ∧ 0 ≤ rightNumber ∧
        leftNumber + rightNumber ≤ 18446744073709551608 := by
      simpa [«bounded_adds_compose:requires/2»] using requires
    let leftValue : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 leftNumber.toNat⟩
    let rightValue : Aeneas.Std.U64 := ⟨BitVec.ofNat 64 rightNumber.toNat⟩
    have leftDecoded : leftValue.val = leftNumber.toNat := by
      simp [leftValue,Aeneas.Std.UScalar.val]
      omega
    have rightDecoded : rightValue.val = rightNumber.toNat := by
      simp [rightValue,Aeneas.Std.UScalar.val]
      omega
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    have pending := Shared.FramedTermAdapter.owned_add_sequence
      (Lynx.Dispatcher.ofTable [] depth) [leftValue,rightValue] 7#u64 44 (by decide)
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero] at pending
    have fits : (7#u64).val + (leftValue.val + rightValue.val) ≤ Aeneas.Std.U64.max := by
      rw [leftDecoded,rightDecoded]
      scalar_tac
    obtain ⟨updated,trace,total⟩ := pending fits
    have returned : Lynx.Result.ReadyPrefix
        (Lynx.apply «bounded_adds_compose:ensures/2» [] depth
          (.integer leftNumber) (.integer rightNumber))
        Shared.FramedTermAdapter.initial (.ok Lynx.Term.true)
        (Shared.FramedTermAdapter.owned updated 48) := by
      let conclude := fun replies : List Lynx.Term => Lynx.Result.ofExcept
        (Erlang.erlang.«==/2» (.tuple replies.toArray) (.tuple #[Lynx.Term.true,Lynx.Term.true]))
      have finished := trace.bind conclude
      simpa [Lynx.apply,«bounded_adds_compose:ensures/2»,
        Shared.FramedTermAdapter.addSequence,conclude,bind_assoc,
        Lynx.Result.ok_bind,Lynx.Rustler.encodeUnsigned,leftDecoded,rightDecoded,
        Int.toNat_of_nonneg bounds.1,Int.toNat_of_nonneg bounds.2.1,
        Shared.FramedTermAdapter.initial] using finished
    exact returned.returns elapsed run terminal
    """
end
