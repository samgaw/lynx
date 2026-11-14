module
public import Atomic.Owned.Funs
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Atomic.OwnedProperties
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
/-- Registration panic must reclaim the already allocated logical atomic cell,
also when explicit owned-drop extraction is selected. -/
theorem rejected (value : U64) :
    counter_new value {} = (.error (.error (.atom "rust_panicked")), {nativeRefCounter := 1}) := by
  simp [counter_new, NativeResourceArc.newOwned, NativeResourceArc.new,
 NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.new, NativeAtomic.dispose, NativeAtomic.lookup, NativeAtomic.typeName,
    NativeM.allocate, NativeM.capturePanic, NativeM.ok, NativeM.fail,
    NativeCodec.roundtrip, Result.handle, Result.bind, Result.ofExcept]

/-- The constructor-only root does not depend on extracting Ordering. -/
theorem registered (value : U64) :
    counter_new value {nativeResourceTypes := [NativeResourceArc.typeName Counter]} =
      (.ok ⟨2,3⟩, {
        nativeResourceTypes := [NativeResourceArc.typeName Counter]
        nativeRefCounter := 3
        nativeHeap := [(3,NativeResourceArc.handleType Counter,.nativeReference 2),
          (2,NativeResourceArc.typeName Counter,
            .tuple #[.integer 1,NativeCodec.encode ({state := ⟨1⟩} : Counter)]),
          (1,NativeAtomic.typeName,NativeCodec.encode value)]}) := by
  simp [counter_new, NativeResourceArc.newOwned, NativeResourceArc.new,
    NativeResourceArc.typeName, NativeResourceArc.handleType, NativeAtomic.new,
    NativeAtomic.typeName, NativeM.allocate, NativeM.ok]

end Atomic.OwnedProperties
