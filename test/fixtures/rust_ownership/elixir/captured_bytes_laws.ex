defmodule LynxCapturedBytesFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxCapturedBytesFixture.Native

  law bytes,
    expects: Native.captured_bytes([0, 128, 255], true) == {:ok, [0, 128, 255]},
    proof: ~LEAN"""
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 8192 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 0, .integer 128, .integer 255]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [0#u8, 128#u8, 255#u8] (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · refine .cons ?_ (.cons ?_ (.cons ?_ (.nil))) <;>
          simp [Lynx.Rustler.decodeUnsigned] <;>
          apply Aeneas.Std.UScalar.eq_of_val_eq <;>
          simp [Aeneas.Std.UScalar.val]
      · decide
      · constructor <;> scalar_tac
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    rw [decoded]
    cbv
    """

  law narrowing,
    expects: Native.captured_bytes([256, 511], true) == {:ok, [0, 255]},
    proof: ~LEAN"""
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 8192 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 256, .integer 511]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [0#u8, 255#u8] (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · refine .cons ?_ (.cons ?_ (.nil)) <;>
          simp [Lynx.Rustler.decodeUnsigned] <;>
          apply Aeneas.Std.UScalar.eq_of_val_eq <;>
          simp [Aeneas.Std.UScalar.val]
      · decide
      · constructor <;> scalar_tac
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    rw [decoded]
    cbv
    """

  law empty,
    expects: Native.captured_bytes([], true) == {:ok, []},
    proof: ~LEAN"""
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 8192 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list []) =
        .ok (Aeneas.Std.alloc.vec.Vec.from ([] : List Aeneas.Std.U8) (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · exact .nil
      · decide
      · constructor <;> scalar_tac
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    rw [decoded]
    cbv
    """

  law panic,
    expects:
      (try do
         Native.captured_bytes([255], false)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 8192 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 255]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [255#u8] (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · refine .cons ?_ (.nil) <;>
          simp [Lynx.Rustler.decodeUnsigned] <;>
          apply Aeneas.Std.UScalar.eq_of_val_eq <;>
          simp [Aeneas.Std.UScalar.val]
      · decide
      · constructor <;> scalar_tac
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    rw [decoded]
    cbv
    """

  law badarg,
    expects:
      (try do
         Native.captured_bytes([4_294_967_296], true)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 8000000 in
    set_option maxRecDepth 8192 in
    have rejected : Lynx.Rustler.decodeUnsigned .U8 32 (.integer 4294967296) =
        .error (.error (.atom "badarg")) := by simp [Lynx.Rustler.decodeUnsigned]
    have decoded := Lynx.Rustler.decodeByteVec_headError
      (.integer 4294967296) Lynx.Term.nil (.error (.atom "badarg")) rejected
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 256)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    cbv
    rw [decoded]
    cbv
    """
end
