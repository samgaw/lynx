module
public import __PREFIX__.Properties
public import __PREFIX__.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace __PREFIX__.Boundary

theorem facade_spec (input : alloc.vec.Vec I64) :
    __FACADE__ input = RustM.ok (input.val.getLast?, __PREFIX__.Properties.retained input) := by
  simpa [__FACADE__] using __PREFIX__.Properties.composition input

theorem records_decoded : Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64)
    (.cons (.integer (-1)) (.cons (.integer 42) .nil)) =
      .ok (alloc.vec.Vec.from [(-1)#i64, 42#i64] (by simp; scalar_tac)) := by
  apply Lynx.Rustler.decodeScalarVec_values (inputs := [.integer (-1), .integer 42]) _ ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) (.cons (by rfl) .nil)

theorem bounds_decoded : Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64)
    (.cons (.integer (-9223372036854775808)) (.cons (.integer 9223372036854775807) .nil)) =
      .ok (alloc.vec.Vec.from [(-9223372036854775808)#i64, 9223372036854775807#i64] (by simp; scalar_tac)) := by
  apply Lynx.Rustler.decodeScalarVec_values (inputs := [.integer (-9223372036854775808), .integer 9223372036854775807]) _ ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) (.cons (by rfl) .nil)

theorem singleton_decoded : Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64)
    (.cons (.integer 0) .nil) = .ok (alloc.vec.Vec.from [0#i64] (by simp; scalar_tac)) := by
  apply Lynx.Rustler.decodeScalarVec_values (inputs := [.integer 0]) _ ?_ (by decide) (by simp; scalar_tac)
  exact .cons (by rfl) .nil

theorem bad_head (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64) (.cons (.atom "false") tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem out_of_range (tail : Lynx.Term) :
    Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64) (.cons (.integer 9223372036854775808) tail) =
      .error (.error (.atom "badarg")) :=
  Lynx.Rustler.decodeScalarVec_headError _ _ _ _ rfl

theorem improper :
    Lynx.Rustler.decodeScalarVec (Lynx.Rustler.decodeSigned .I64 64) (.cons (.integer 0) (.integer 7)) =
      .error (.error (.atom "nif_panicked")) :=
  Lynx.Rustler.decodeScalarVec_improper _ _ (0#i64) _ rfl

end __PREFIX__.Boundary
