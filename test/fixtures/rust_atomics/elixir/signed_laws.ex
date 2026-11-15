defmodule LynxSignedFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law negative_credit,
    expects: LynxSignedFixture.Native.signed_adjust(-7, 3) == {true, -4},
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «negative_credit:ensures/0», Elixir.LynxSignedFixture.Native.«signed_adjust/2»,
      Elixir.LynxSignedFixture.Native.«signed_adjust:execution/2»,
      Signed.Properties.facade_contract, Signed.Properties.locked_contract, Signed.Properties.adjusted_eq]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law negative_debit,
    expects: LynxSignedFixture.Native.signed_adjust(7, -11) == {true, -4},
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «negative_debit:ensures/0», Elixir.LynxSignedFixture.Native.«signed_adjust/2»,
      Elixir.LynxSignedFixture.Native.«signed_adjust:execution/2»,
      Signed.Properties.facade_contract, Signed.Properties.locked_contract, Signed.Properties.adjusted_eq]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law cross_zero,
    expects: LynxSignedFixture.Native.signed_adjust(-7, 11) == {true, 4},
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «cross_zero:ensures/0», Elixir.LynxSignedFixture.Native.«signed_adjust/2»,
      Elixir.LynxSignedFixture.Native.«signed_adjust:execution/2»,
      Signed.Properties.facade_contract, Signed.Properties.locked_contract, Signed.Properties.adjusted_eq]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law positive_overflow,
    expects:
      LynxSignedFixture.Native.signed_adjust(9_223_372_036_854_775_807, 1) ==
        {false, 9_223_372_036_854_775_807},
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «positive_overflow:ensures/0», Elixir.LynxSignedFixture.Native.«signed_adjust/2»,
      Elixir.LynxSignedFixture.Native.«signed_adjust:execution/2»,
      Signed.Properties.facade_contract, Signed.Properties.locked_contract, Signed.Properties.adjusted_eq]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law negative_overflow,
    expects:
      LynxSignedFixture.Native.signed_adjust(-9_223_372_036_854_775_808, -1) ==
        {false, -9_223_372_036_854_775_808},
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    simp only [Lynx.apply, «negative_overflow:ensures/0», Elixir.LynxSignedFixture.Native.«signed_adjust/2»,
      Elixir.LynxSignedFixture.Native.«signed_adjust:execution/2»,
      Signed.Properties.facade_contract, Signed.Properties.locked_contract, Signed.Properties.adjusted_eq]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law above_range,
    expects:
      (try do
         LynxSignedFixture.Native.signed_adjust(9_223_372_036_854_775_808, 0)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law below_range,
    expects:
      (try do
         LynxSignedFixture.Native.signed_adjust(-9_223_372_036_854_775_809, 0)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """

  law invalid_delta,
    expects:
      (try do
         LynxSignedFixture.Native.signed_adjust(0, false)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    """
end
