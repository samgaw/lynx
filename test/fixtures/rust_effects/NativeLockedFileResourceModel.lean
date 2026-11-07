module
public import LockedFileResource.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace LockedFileResource.Properties
open NativeFile

@[expose] def Valid (state : State) : Prop :=
  state.visible.size ≤ limit ∧ state.durable.size ≤ limit ∧ state.position ≤ limit

theorem decode_valid (state : State) (valid : Valid state) :
    decode (encode state) = some state := by
  obtain ⟨visible, durable, position⟩ := valid
  simp [decode, encode, not_lt.mpr visible, not_lt.mpr durable, not_lt.mpr position]

@[expose] def payload : effects_native.LockedFileResource := ⟨⟨2⟩⟩
@[expose] def fileCell (state : State) : Nat × String × Term := (1, typeName, encode state)
@[expose] def closedCell (state : State) : Nat × String × Term := (1, closedTypeName, encode state)
@[expose] def mutexCell : Nat × String × Term :=
  (2, NativeMutex.typeName NativeFile, .tuple #[.atom "unlocked", .atom "unpoisoned", .reference 1])

@[expose] def initial (env : Environment) (state : State) : Environment :=
  {env with refCounter := 1, nativeHeap := [fileCell state]}

@[expose] def live (env : Environment) (state : State) : Environment :=
  {env with refCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType effects_native.LockedFileResource, .reference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), mutexCell, fileCell state]}

@[expose] def cleaned (env : Environment) (state : State) : Environment :=
  {env with refCounter := 4, nativeHeap := [
    (4, NativeResourceArc.handleType effects_native.LockedFileResource, .reference 3),
    (3, NativeResourceArc.typeName effects_native.LockedFileResource,
      .tuple #[.integer 1, NativeCodec.encode payload]), closedCell state]}

@[expose] def retired (env : Environment) (state : State) (counter : Nat := 4) : Environment :=
  {env with refCounter := counter, nativeHeap := [closedCell state]}

/-- The actual compiler destructor calls the owning Mutex<File> primitive. -/
theorem cleanup_contract (value : effects_native.LockedFileResource) :
    effects_native.LockedFileResource.drop_owned value = NativeMutex.disposeFile value.state := rfl

theorem cleanup_ready {α : Type} (value : effects_native.LockedFileResource)
    (file : NativeFile) (poisoned : Bool) (env after : Environment)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == value.state.id) =
      [(value.state.id, NativeMutex.typeName NativeFile,
        .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
          NativeCodec.encode file])])
    (ready : pollClose file env = some (.ok (), after))
    (retained : after.nativeHeap.filter (fun cell => cell.1 == value.state.id) =
      [(value.state.id, NativeMutex.typeName NativeFile,
        .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
          NativeCodec.encode file])])
    (next : Unit → NativeM α) :
    (effects_native.LockedFileResource.drop_owned value >>= next) env =
      next () {after with nativeHeap := after.nativeHeap.filter (fun cell => cell.1 != value.state.id)} := by
  rw [cleanup_contract]
  exact NativeMutex.disposeFile_next value.state file poisoned env after stored ready retained next

end LockedFileResource.Properties
