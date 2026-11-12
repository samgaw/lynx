module
public import OwnedTreeNative.DriverProperties
public import OwnedTreeNative.RustlerBridge
public section
open Aeneas Aeneas.Std
namespace OwnedTreeNative.NativeProperties

theorem facade (payload : alloc.vec.Vec U8) (budget : U16) :
    __FACADE__ payload budget =
      RustM.ok (if 2 ≤ budget.val then some 2#u16 else none) :=
  OwnedTreeNative.Properties.binary_tree_nodes payload budget

@[expose] def sample : alloc.vec.Vec U8 := alloc.vec.Vec.from [0#u8, 255#u8] (by simp; scalar_tac)

theorem sample_decoded : Lynx.Rustler.decodeByteVec
    (.cons (.integer 0) (.cons (.integer 255) .nil)) = .ok sample := by
  unfold sample
  apply Lynx.Rustler.decodeByteVec_values (.cons rfl (.cons rfl .nil)) (by decide) (by simp; scalar_tac)

end OwnedTreeNative.NativeProperties
