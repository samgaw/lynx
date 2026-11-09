module
public import Resource.Facade.Funs
public import Resource.RustlerBridge
public import Lynx.Rustler
public section
open Lynx Aeneas Aeneas.Std effects_native
namespace Resource.Properties

theorem reader (counter : effects_core.Counter) : effects_core.counter_value counter = .ok counter.value := rfl

theorem resource_reader (resource : NativeResourceArc ScalarResource) :
    scalar_resource_read resource = (do let contents ← NativeResourceArc.deref resource; Result.ok contents.counter.value) := by
  simp [scalar_resource_read, reader, NativeM.ok]

theorem facade_continuation {β : Type} (value : U64) (next : Term → Result β)
    (env : Environment) (registered : NativeResourceArc.typeName ScalarResource ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) (choices : List ScheduleChoice) :
    (Rustler.executeNative (__NIF__ value) Rustler.encodeUnsigned >>= next).run env choices =
      (next (.integer value.val)).run { env with nativeRefCounter := env.nativeRefCounter + 3 } choices := by
  simp [NativeResourceArc.typeName] at registered
  simp only [__NIF__, scalar_resource_cycle, scalar_resource_new, scalar_resource_clone,
    resource_reader, NativeDrop.drop, NativeM.ok, Rustler.executeNative, bind_assoc]
  simp only [NativeResourceArc.new, Result.nativeGet_bind, Result.handle]
  simp [NativeResourceArc.clone, NativeResourceArc.release, NativeResourceArc.takeOwner,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState, NativeResourceArc.deref,
    NativeResourceArc.ownership, NativeM.allocate, Result.handle, registered, empty, bind_assoc,
    NativeCodec.roundtrip, NativeResourceArc.referenceLimit, NativeResourceArc.handleType,
    NativeResourceArc.typeName, Nat.add_assoc, Rustler.encodeUnsigned]
end Resource.Properties
