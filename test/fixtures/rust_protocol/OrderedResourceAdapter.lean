module
public import __PREFIX__.Properties
public import __PREFIX__.ResourceProperties
public section
open Aeneas Aeneas.Std Lynx experiment_nif
open __PREFIX__.Extraction.OrderedCollections
namespace __PREFIX__.NifProperties

theorem create_contract :
    __NEW__ = (do
      let table ← NativeMutex.new mapNew
      let claims ← NativeMutex.new setNew
      NativeResourceArc.newOwned (RegistryState.mk table claims)) := rfl

theorem replace_contract (owner : NativeResourceArc RegistryState) (key value : U64) :
    __REPLACE__ owner key value = (do
      let state ← NativeResourceArc.deref owner
      let previous ← experiment_analysis.registry_replace state.table key value
      NativeResourceArc.releaseOwned owner
      .ok previous) := by
  simp [__REPLACE__, NativeOwnedDrop.drop, NativeM.ok]

theorem take_contract (owner : NativeResourceArc RegistryState) (key : U64) :
    __TAKE__ owner key = (do
      let state ← NativeResourceArc.deref owner
      let previous ← experiment_analysis.registry_take state.table key
      NativeResourceArc.releaseOwned owner
      .ok previous) := by
  simp [__TAKE__, NativeOwnedDrop.drop, NativeM.ok]

theorem claim_contract (owner : NativeResourceArc RegistryState) (key : U64) :
    __CLAIM__ owner key = (do
      let state ← NativeResourceArc.deref owner
      let claimed ← experiment_analysis.registry_claim state.claims key
      NativeResourceArc.releaseOwned owner
      .ok claimed) := by
  simp [__CLAIM__, NativeOwnedDrop.drop, NativeM.ok]
end __PREFIX__.NifProperties
