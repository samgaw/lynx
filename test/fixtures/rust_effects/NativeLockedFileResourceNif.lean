module
public import LockedFileResource.Model
public import LockedFileResource.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace LockedFileResource.NifProperties
open LockedFileResource.Properties NativeFile

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeFile.typeName NativeFile.closedTypeName List.filter

@[expose] def pinnedEnv (env : Environment) (state : State) : Environment :=
  {env with refCounter := 6, nativeHeap :=
    NativeResourceArc.vmCells payload 3 5 6 ++ [mutexCell, fileCell state]}

@[expose] def decodedEnv (env : Environment) (state : State) : Environment :=
  {env with refCounter := 7, nativeHeap := [
    (7, NativeResourceArc.handleType effects_native.LockedFileResource, .reference 3),
    (6, NativeResourceArc.termType effects_native.LockedFileResource, .tuple #[.reference 3, .reference 5]),
    (5, NativeResourceArc.handleType effects_native.LockedFileResource, .reference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 2, NativeCodec.encode payload]), mutexCell, fileCell state]}

theorem pin (env : Environment) (state : State) :
    NativeResourceArc.Pinned payload 3 5 6 (pinnedEnv env state) := by
  constructor
  · simp [pinnedEnv]
  · intro c member
    simp only [pinnedEnv, NativeResourceArc.vmCells, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> simp [pinnedEnv, mutexCell, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, mutexCell, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, mutexCell, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, mutexCell, fileCell]
  · simp [pinnedEnv, NativeResourceArc.vmCells, mutexCell, fileCell, NativeFile.encode,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType]

theorem decode_next {α : Type} (env : Environment) (state : State)
    (next : NativeResourceArc effects_native.LockedFileResource → NativeM α)
    (registered : NativeResourceArc.typeName effects_native.LockedFileResource ∈ env.nativeResourceTypes) :
    (NativeResourceArc.decode (.reference 6) >>= next) (pinnedEnv env state) =
      next ⟨3,7⟩ (decodedEnv env state) := by
  have decoded := NativeResourceArc.decode_pinned_next payload next (pinnedEnv env state)
    3 5 6 (pin env state) registered
  simpa [pinnedEnv, decodedEnv, NativeResourceArc.vmCells, mutexCell, fileCell, List.map] using decoded

/-- The compiled export consumes its decoded Rust owner. The still-live VM pin
keeps the file open, and no close outcome is consumed. Rust unit encodes as {}. -/
theorem release_call (env : Environment) (state : State)
    (registered : NativeResourceArc.typeName effects_native.LockedFileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])) (pinnedEnv env state) =
      (.ok (.tuple #[]), {pinnedEnv env state with refCounter := 7}) := by
  rw [decode_next env state _ registered]
  simp only [__RELEASE__, locked_file_resource_release, monadLift_self, NativeOwnedDrop.drop,
    Rustler.executeNative]
  have released := NativeResourceArc.releaseOwned_retained_handled_next
    (⟨3,7⟩ : NativeResourceArc effects_native.LockedFileResource) payload
    (Result.ok (Term.tuple #[]))
    (fun error => match error with
      | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
      | _ => Result.error .exhausted)
    Result.ok (decodedEnv env state)
    (by simp [decodedEnv, mutexCell, fileCell]) (by simp [decodedEnv, mutexCell, fileCell])
    (by simp [decodedEnv, mutexCell, fileCell, NativeFile.encode,
      NativeResourceArc.typeName, NativeResourceArc.handleType, NativeResourceArc.termType])
  convert released using 1 <;> simp [decodedEnv, pinnedEnv, NativeResourceArc.vmCells, mutexCell, fileCell,
    Result.bind_ok, Result.ok_apply, Result.handle, List.filter, List.map]
  all_goals congr 1

/-- A valid file remains usable after the NIF has released its temporary owner. -/
theorem release_preserves_file (env : Environment) (state : State) (valid : Valid state)
    (registered : NativeResourceArc.typeName effects_native.LockedFileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.reference 6)
      Rustler.executeNative (__RELEASE__ owner) (fun _ => .tuple #[])) (pinnedEnv env state) =
      (.ok (.tuple #[]), {pinnedEnv env state with refCounter := 7}) ∧
    lookup ⟨1⟩ {pinnedEnv env state with refCounter := 7} = some state ∧
    ({pinnedEnv env state with refCounter := 7} : Environment).nativeHeap.filter
      (fun cell => cell.1 == 2) = [mutexCell] := by
  refine ⟨release_call env state registered, ?_, ?_⟩
  all_goals simp [lookup, pinnedEnv, NativeResourceArc.vmCells, mutexCell, fileCell, decode_valid state valid]

end LockedFileResource.NifProperties
