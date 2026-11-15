module
public import LockedBytes.Properties
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace LockedBytes.NifProperties

theorem facade_view (input : Rustler.Binary) (view : Slice U8)
    (decoded : Rustler.binaryAsSlice input = RustM.ok view) :
    __COPY__ input = (do
      let bytes ← atomic_analysis.copy_locked view
      NativeResourceArc.newOwned (⟨bytes⟩ : ByteBuffer)) := by
  simp [__COPY__, decoded, NativeM.lift, NativeM.ok]

end LockedBytes.NifProperties
