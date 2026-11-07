module
public import SharedWrite.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace SharedWrite.Properties
open NativeFile

/-- The cross-crate resource helper calls the actual extracted shared-file writer. -/
theorem cross_contract (owner : NativeResourceArc effects_native.FileResource) (data : Slice U8) :
    file_resource_write owner data = (do
      let resource ← NativeResourceArc.deref owner
      effects_core.write_shared_file resource.file data) := rfl

/-- A shared write preserves the handle identity and follows the actual partial-write transition. -/
theorem write_next {α : Type} (file : NativeFile) (data : Slice U8) (env : Environment)
    (before after : State) (reply : core.result.Result Usize NativeIoError)
    (found : lookup file env = some before) (writable : getHandle file handleTypeName env = none)
    (ready : blocked before = false) (step : writeStep before data = some (reply,after))
    (next : core.result.Result Usize NativeIoError → NativeM α) :
    (effects_core.write_shared_file file data >>= next) env = next reply (store file after env) := by
  have poll : pollWrite file data env = some (.ok (reply,file),store file after env) := by
    simp only [pollWrite,found,ready,Bool.false_eq_true,↓reduceIte,step,writable]
  simp only [effects_core.write_shared_file,monadLift_self,write,Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [NativeM.ok]

end SharedWrite.Properties
