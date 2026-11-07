module
public import FileResource.Model
public import FileResource.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.NifProperties
open FileResource.Properties NativeFile

@[expose] def pinnedEnv (env : Environment) (state : State) : Environment :=
  {env with refCounter := 5, nativeHeap :=
    NativeResourceArc.vmCells payload 2 4 5 ++ [fileCell state]}

@[expose] def decodedEnv (env : Environment) (state : State) : Environment :=
  {env with refCounter := 6, nativeHeap := [
    (6, NativeResourceArc.handleType effects_native.FileResource, .reference 2),
    (5, NativeResourceArc.termType effects_native.FileResource, .tuple #[.reference 2, .reference 4]),
    (4, NativeResourceArc.handleType effects_native.FileResource, .reference 2),
    (2, NativeResourceArc.typeName effects_native.FileResource,
      .tuple #[.integer 2, NativeCodec.encode payload]), fileCell state]}

theorem pin (env : Environment) (state : State) :
    NativeResourceArc.Pinned payload 2 4 5 (pinnedEnv env state) := by
  constructor
  · simp [pinnedEnv]
  · intro c member
    simp only [pinnedEnv, NativeResourceArc.vmCells, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [pinnedEnv, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, fileCell, NativeFile.encode,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType]

theorem decode_next {α : Type} (env : Environment) (state : State)
    (next : NativeResourceArc effects_native.FileResource → NativeM α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (NativeResourceArc.decode (.reference 5) >>= next) (pinnedEnv env state) =
      next ⟨2,6⟩ (decodedEnv env state) := by
  have decoded := NativeResourceArc.decode_pinned_next payload next (pinnedEnv env state)
    2 4 5 (pin env state) registered
  simpa [pinnedEnv, decodedEnv, NativeResourceArc.vmCells, fileCell, List.map] using decoded

/-- The compiled export consumes its decoded Rust owner. The still-live VM pin
keeps the file open, and no close outcome is consumed. Rust unit encodes as {}. -/
theorem release_call (env : Environment) (state : State)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 5)
      Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])) (pinnedEnv env state) =
      (.ok (.tuple #[]), {pinnedEnv env state with refCounter := 6}) := by
  rw [decode_next env state _ registered]
  simp only [__RELEASE__, file_resource_release, monadLift_self, NativeOwnedDrop.drop,
    Rustler.executeNative]
  have released := NativeResourceArc.releaseOwned_retained_handled_next
    (⟨2,6⟩ : NativeResourceArc effects_native.FileResource) payload
    (Result.ok (Term.tuple #[]))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted)
    Result.ok (decodedEnv env state)
    (by simp [decodedEnv, fileCell]) (by simp [decodedEnv, fileCell])
    (by simp [decodedEnv, fileCell, NativeFile.encode,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType])
  convert released using 1 <;> simp [decodedEnv, pinnedEnv, NativeResourceArc.vmCells, fileCell,
    Result.bind_ok, Result.ok_apply, Result.handle, List.filter, List.map]
  all_goals congr 1

/-- A valid file remains usable after the NIF has released its temporary owner. -/
theorem release_preserves_file (env : Environment) (state : State) (valid : Valid state)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 5)
      Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])) (pinnedEnv env state) =
      (.ok (.tuple #[]), {pinnedEnv env state with refCounter := 6}) ∧
    lookup ⟨1⟩ {pinnedEnv env state with refCounter := 6} = some state := by
  refine ⟨release_call env state registered, ?_⟩
  simp [lookup, pinnedEnv, NativeResourceArc.vmCells, fileCell, decode_valid state valid]

end FileResource.NifProperties
