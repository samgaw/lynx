module
public import FileResource.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Properties
open NativeFile

@[expose] def Valid (state : State) : Prop :=
  state.visible.size ≤ limit ∧ state.durable.size ≤ limit ∧ state.position ≤ limit

theorem decode_valid (state : State) (valid : Valid state) :
    decode (encode state) = some state := by
  obtain ⟨visible, durable, position⟩ := valid
  simp [decode, encode, not_lt.mpr visible, not_lt.mpr durable, not_lt.mpr position]

@[expose] def payload : effects_native.FileResource := ⟨⟨1⟩⟩
@[expose] def fileCell (state : State) : Nat × String × Term := (1, typeName, encode state)
@[expose] def closedCell (state : State) : Nat × String × Term := (1, closedTypeName, encode state)

@[expose] def initial (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [fileCell state]}

@[expose] def live (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 3, nativeHeap := [
    (3, NativeResourceArc.handleType effects_native.FileResource, .nativeReference 2),
    (2, NativeResourceArc.typeName effects_native.FileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), fileCell state]}

@[expose] def cleaned (env : Environment) (state : State) : Environment :=
  {env with nativeRefCounter := 3, nativeHeap := [
    (3, NativeResourceArc.handleType effects_native.FileResource, .nativeReference 2),
    (2, NativeResourceArc.typeName effects_native.FileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), closedCell state]}

@[expose] def retired (env : Environment) (state : State) (counter : Nat := 3) : Environment :=
  {env with nativeRefCounter := counter, nativeHeap := [closedCell state]}

/-- This is the actual optimized compiler destructor, not a substitute cleanup. -/
theorem cleanup_contract (value : effects_native.FileResource) :
    effects_native.FileResource.drop_owned value = NativeFile.close value.file := rfl

theorem cleanup_ready {α : Type} (value : effects_native.FileResource) (env : Environment)
    (before after : State) (registered : lookup value.file env = some before)
    (ready : blocked before = false) (step : closeStep before = some after)
    (next : Unit → NativeM α) :
    (effects_native.FileResource.drop_owned value >>= next) env =
      next () (retire value.file after env) := by
  have poll : pollClose value.file env = some (.ok (), retire value.file after env) := by
    simp [pollClose, registered, ready, step]
  rw [cleanup_contract]
  simp only [close, Result.wait_bind]
  rw [Result.wait_ready_run _ _ _ _ _ poll]
  simp only [Result.ok_bind]

end FileResource.Properties
