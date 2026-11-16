defmodule LynxCapturedFrameFixture.Laws do
  @compile :debug_info
  use Lynx.Laws
  alias LynxCapturedFrameFixture.Native

  law complete,
    expects:
      Native.captured_frame([1, 0, 2, 128, 255, 1, 0, 0], true) == {:ok, [1, 0, 2, 128, 255]},
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 1, .integer 0, .integer 2, .integer 128, .integer 255, .integer 1, .integer 0, .integer 0]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [1#u8, 0#u8, 2#u8, 128#u8, 255#u8, 1#u8, 0#u8, 0#u8] (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil)))))))) <;>
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

  law incomplete,
    expects: Native.captured_frame([1, 0, 2, 128], true) == {:ok, nil},
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 1, .integer 0, .integer 2, .integer 128]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [1#u8, 0#u8, 2#u8, 128#u8] (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil)))) <;>
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

  law wrong_version,
    expects: Native.captured_frame([2, 0, 0], true) == {:error, 1},
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 2, .integer 0, .integer 0]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [2#u8, 0#u8, 0#u8] (by scalar_tac)) := by
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

  law empty,
    expects: Native.captured_frame([], true) == {:ok, nil},
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list []) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [] (by scalar_tac)) := by
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

  law rejected,
    expects:
      (try do
         Native.captured_frame([1, 0, 1, 255], false)
         false
       catch
         :error, :nif_panicked -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
    have decoded : Lynx.Rustler.decodeByteVec (Lynx.Term.list [.integer 1, .integer 0, .integer 1, .integer 255]) =
        .ok (Aeneas.Std.alloc.vec.Vec.from [1#u8, 0#u8, 1#u8, 255#u8] (by scalar_tac)) := by
      apply Lynx.Rustler.decodeByteVec_values
      · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ (.nil)))) <;>
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
         Native.captured_frame([4_294_967_296], true)
         false
       catch
         :error, :badarg -> true
       end),
    proof: ~LEAN"""
    set_option maxHeartbeats 12000000 in
    set_option maxRecDepth 16384 in
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
