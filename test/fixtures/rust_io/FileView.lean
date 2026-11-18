module
public import Record.ResizeProperties

public section

open Lynx NativeFile

namespace Record

/-- A view of the heap for the operations of one writable descriptor.
The laws refer to the executable NativeFile operations. -/
class FileView where
  render : Environment → NativeFile → State → List (Nat × String × Term) → Environment
  Separated : NativeFile → List (Nat × String × Term) → Prop
  load_rendered : ∀ env file state frame, Separated file frame →
    ResizeProperties.Admitted state → lookup file (render env file state frame) = some state
  store_rendered : ∀ env file before after frame, Separated file frame →
    ResizeProperties.Admitted before → store file after (render env file before frame) = render env file after frame
  readOnly_rendered : ∀ env file state frame, Separated file frame →
    getHandle file handleTypeName (render env file state frame) = none
  render_pid : ∀ env file state frame, (render env file state frame).currentPid = env.currentPid

attribute [simp] FileView.render_pid

namespace FileView

theorem initial_view [FileView] (env : Environment) (file : NativeFile)
    (state : State) (frame : List (Nat × String × Term)) (elapsed : PID → Nat → Nat) :
    (Concurrent.State.initial (render env file state frame) elapsed).nativeView env.currentPid =
      render env file state frame := by
  rw [← render_pid env file state frame]
  generalize render env file state frame = world
  cases world
  simp [Concurrent.State.nativeView, Concurrent.State.view, Concurrent.State.process,
    Concurrent.State.initial]

open Record.Properties (HeapLayout fileEnv Separate store_at no_shared_handle_at)
open Record.ResizeProperties (Admitted decode_admitted lookup_admitted)

@[instance_reducible] instance (priority := low) independent [HeapLayout] : FileView where
  render := fileEnv
  Separated := Separate
  load_rendered := lookup_admitted
  store_rendered := fun env file before after frame separates _ =>
    store_at env file before after frame separates
  readOnly_rendered := no_shared_handle_at
  render_pid := fun _ _ _ _ => rfl

theorem admits_valid (state : State) (valid : Record.Properties.Valid state) : Admitted state :=
  ⟨valid.1, valid.2.1.trans valid.1, valid.2.2⟩

@[expose] def inodeCell (number : Nat) (state : State) : Nat × String × Term :=
  (number, inodeTypeName, encode {state with position := 0, script := .nil})

@[expose] def handleCell (number : Nat) (file : NativeFile) (state : State) : Nat × String × Term :=
  (file.id, writableHandleTypeName, encodeHandle ⟨number, state.position, state.script⟩)

@[expose] def namedWorld (number : Nat) (env : Environment) (file : NativeFile) (state : State)
    (frame : List (Nat × String × Term)) : Environment :=
  { env with
    nativeRefCounter := max env.nativeRefCounter (max file.id number)
    nativeHeap := handleCell number file state :: frame ++ [inodeCell number state] }

@[expose] def NamedSeparated (number : Nat) (file : NativeFile) (frame : List (Nat × String × Term)) : Prop :=
  file.id ≠ 0 ∧ number ≠ 0 ∧ file.id ≠ number ∧
    Separate file frame ∧ Separate ⟨number⟩ frame

private theorem filter_absent (frame : List (Nat × String × Term)) (id : Nat)
    (separate : Separate ⟨id⟩ frame) : frame.filter (fun cell => cell.1 == id) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro cell member
  simpa using separate cell member

theorem named_inode (number : Nat) (env : Environment) (file : NativeFile)
    (state : State) (frame : List (Nat × String × Term))
    (separate : NamedSeparated number file frame) (valid : Admitted state) :
    inode number (namedWorld number env file state frame) =
      some {state with position := 0, script := .nil} := by
  obtain ⟨_, nodeNonzero, different, _, nodeFrame⟩ := separate
  have byNode := filter_absent frame number nodeFrame
  have nodeBound : number ≤ max env.nativeRefCounter (max file.id number) := by omega
  have inodeValid : Admitted {state with position := 0, script := .nil} :=
    ⟨valid.1, valid.2.1, Nat.zero_le _⟩
  simp [namedWorld, inode, handleCell, inodeCell, byNode, nodeNonzero, different,
    not_lt.mpr nodeBound, List.filter_append, decode_admitted _ inodeValid]

theorem named_load (number : Nat) (env : Environment) (file : NativeFile)
    (state : State) (frame : List (Nat × String × Term))
    (separate : NamedSeparated number file frame) (valid : Admitted state) :
    lookup file (namedWorld number env file state frame) = some state := by
  obtain ⟨fileNonzero, nodeNonzero, different, fileFrame, nodeFrame⟩ := separate
  have byFile := filter_absent frame file.id fileFrame
  have byNode := filter_absent frame number nodeFrame
  have fileBound : file.id ≤ max env.nativeRefCounter (max file.id number) := by omega
  have nodeBound : number ≤ max env.nativeRefCounter (max file.id number) := by omega
  have inodeValid : Admitted {state with position := 0, script := .nil} :=
    ⟨valid.1, valid.2.1, Nat.zero_le _⟩
  simp [namedWorld, lookup, sharedLookup, getHandle, inode, handleCell, inodeCell,
    byFile, byNode, fileBound, nodeBound, not_lt.mpr fileBound, not_lt.mpr nodeBound,
    fileNonzero, nodeNonzero, different, Ne.symm different, List.filter_append, decodeHandle,
    encodeHandle, decode_admitted _ inodeValid, not_lt.mpr valid.2.2,
    not_lt.mpr (Int.natCast_nonneg state.position),
    typeName, writableHandleTypeName, handleTypeName]

theorem named_store (number : Nat) (env : Environment) (file : NativeFile)
    (before after : State) (frame : List (Nat × String × Term))
    (separate : NamedSeparated number file frame) (valid : Admitted before) :
    store file after (namedWorld number env file before frame) =
      namedWorld number env file after frame := by
  obtain ⟨_, nodeNonzero, different, fileFrame, nodeFrame⟩ := separate
  have byFile := filter_absent frame file.id fileFrame
  have fixed : frame.map (fun cell =>
      if cell.1 = file.id then
        (file.id, cell.2.1, encodeHandle ⟨number, after.position, after.script⟩)
      else if cell.1 = number then inodeCell number after else cell) = frame := by
    conv_rhs => rw [← List.map_id frame]
    apply List.map_congr_left
    intro cell member
    simp [fileFrame cell member, nodeFrame cell member]
  simp [inodeCell, encodeHandle] at fixed
  simp [namedWorld, store, sharedStore, handleCell, inodeCell,
    byFile, different, Ne.symm different, List.filter_append,
    List.map_append, decodeHandle, encodeHandle, nodeNonzero, not_lt.mpr valid.2.2,
    not_lt.mpr (Int.natCast_nonneg before.position),
    typeName, writableHandleTypeName, handleTypeName, fixed]

theorem named_writable (number : Nat) (env : Environment) (file : NativeFile)
    (state : State) (frame : List (Nat × String × Term))
    (separate : NamedSeparated number file frame) :
    getHandle file handleTypeName (namedWorld number env file state frame) = none := by
  obtain ⟨fileNonzero, _, different, fileFrame, _⟩ := separate
  have byFile := filter_absent frame file.id fileFrame
  have fileBound : file.id ≤ max env.nativeRefCounter (max file.id number) := by omega
  simp [namedWorld, getHandle, handleCell, inodeCell, byFile, fileNonzero,
    different, Ne.symm different, not_lt.mpr fileBound, List.filter_append,
    writableHandleTypeName, handleTypeName]

@[expose, instance_reducible] def named (number : Nat) : FileView where
  render := namedWorld number
  Separated := NamedSeparated number
  load_rendered := named_load number
  store_rendered := named_store number
  readOnly_rendered := named_writable number
  render_pid := fun _ _ _ _ => rfl

theorem named_separated (number : Nat) (file : NativeFile)
    (frame : List (Nat × String × Term)) :
    @Separated (named number) file frame ↔ NamedSeparated number file frame :=
  Iff.rfl

theorem named_render (number : Nat) (env : Environment) (file : NativeFile) (state : State)
    (frame : List (Nat × String × Term)) :
    @render (named number) env file state frame = namedWorld number env file state frame :=
  rfl

end FileView
end Record
