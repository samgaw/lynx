module
public import Owned.Extraction.Funs
public section
open Aeneas Aeneas.Std effects_native Lynx
namespace Owned.Properties

theorem construct (value : U64) :
    owned_counter_payload value = (do
      let mutex ← NativeMutex.new ({ value } : effects_core.Counter)
      Result.ok ⟨mutex⟩) := rfl

/-- The actual compiler-generated destructor consumes the stored mutex identity. -/
theorem cleanup (payload : CounterResource) :
    CounterResource.drop_owned payload = NativeMutex.dispose payload.state := rfl

/-- Construction followed by actual compiler cleanup reclaims the cell and preserves
all unrelated environment fields, without recycling the allocation identity. -/
theorem construct_cleanup (value : U64) (env : Environment)
    (fresh : env.nativeHeap.any (fun cell => cell.1 == env.nativeRefCounter + 1) = false) :
    (owned_counter_payload value >>= CounterResource.drop_owned) env =
      (.ok (), { env with nativeRefCounter := env.nativeRefCounter + 1 }) := by
  simpa [owned_counter_payload, CounterResource.drop_owned, NativeOwnedDrop.drop,
    NativeM.ok, bind_assoc] using
    NativeMutex.new_dispose ({ value } : effects_core.Counter) env fresh

end Owned.Properties
