module
public import Open.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Open.Properties
open NativeFile

@[expose] def path : Str := Slice.from [100#u8, 97#u8, 116#u8, 97#u8] (by scalar_tac)
@[expose] def nameBytes : ByteArray := ⟨#[100,97,116,97]⟩
@[expose] def choice (success : Bool) (error : Nat) (script rest : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring nameBytes 0,
    .atom (if success then "ok" else "error"), .integer error, script]) rest
@[expose] def namespaceCell (script : Term) : Nat × String × Term :=
  (0, namespaceTypeName, encodeNamespace ⟨[(nameBytes,1)], [(nameBytes,1)], [], script⟩)
@[expose] def nodeCell (state : State) : Nat × String × Term :=
  (1, inodeTypeName, encode {state with position := 0, script := .nil})
@[expose] def initial (state : State) (script : Term) : Environment :=
  {nativeRefCounter := 1, nativeHeap := [namespaceCell script, nodeCell state]}
@[expose] def opened (state : State) (script rest : Term) : Environment :=
  {nativeRefCounter := 2, nativeHeap := [
    (2, handleTypeName, encodeHandle ⟨1,0,script⟩), namespaceCell rest, nodeCell state]}

theorem path_bytes : bytes path = nameBytes := by
  simp [bytes, path, Slice.from, Slice.val, nameBytes]
  decide

theorem valid_name : supportedPath nameBytes = true := by decide

theorem not_directory : (nameBytes.data == #[46]) = false := by decide

theorem core_open_next {α : Type} (state : State) (script rest : Term)
    (visible : state.visible.size ≤ limit) (durable : state.durable.size ≤ limit)
    (next : core.result.Result NativeFile NativeIoError → NativeM α) :
    (io_core.open_readonly path >>= next) (initial state (choice true 0 script rest)) =
      next (.Ok ⟨2⟩) (opened state script rest) := by
  have poll : pollOpenReadOnly path (initial state (choice true 0 script rest)) =
      some (.ok (.Ok ⟨2⟩), opened state script rest) := by
    simp [pollOpenReadOnly, supportedOpenPath, path_bytes, valid_name, not_directory, initial, namespaceCell, nodeCell,
      namespaceState, namespaceSnapshot, namespaceTable, namespaceHistory,
      encodeNamespace, encodeNames, tablesEqual, namespaceEntry, List.eraseDups_cons, choice, openChoice, pathChoice, inode, decode, encode,
      not_lt.mpr visible, not_lt.mpr durable, replaceNamespaceScript, opened,
      handleTypeName, namespaceTypeName, encodeHandle]
  simp only [io_core.open_readonly, monadLift_self,
    openReadOnly, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

@[expose] def openedPair (state : State) (firstScript secondScript rest : Term) : Environment :=
  {nativeRefCounter := 3, nativeHeap := [
    (3, handleTypeName, encodeHandle ⟨1,0,secondScript⟩),
    (2, handleTypeName, encodeHandle ⟨1,0,firstScript⟩),
    namespaceCell rest, nodeCell state]}

theorem core_open_again_next {α : Type} (state : State) (firstScript secondScript rest : Term)
    (visible : state.visible.size ≤ limit) (durable : state.durable.size ≤ limit)
    (next : core.result.Result NativeFile NativeIoError → NativeM α) :
    (io_core.open_readonly path >>= next)
      (opened state firstScript (choice true 0 secondScript rest)) =
      next (.Ok ⟨3⟩) (openedPair state firstScript secondScript rest) := by
  have poll : pollOpenReadOnly path
      (opened state firstScript (choice true 0 secondScript rest)) =
      some (.ok (.Ok ⟨3⟩), openedPair state firstScript secondScript rest) := by
    simp [pollOpenReadOnly, supportedOpenPath, path_bytes, valid_name, not_directory, opened, namespaceCell, nodeCell,
      namespaceState, namespaceSnapshot, namespaceTable, namespaceHistory,
      encodeNamespace, encodeNames, tablesEqual, namespaceEntry, List.eraseDups_cons, choice, openChoice, pathChoice, inode, decode, encode,
      not_lt.mpr visible, not_lt.mpr durable, replaceNamespaceScript, openedPair,
      handleTypeName, namespaceTypeName, inodeTypeName, encodeHandle]
  simp only [io_core.open_readonly, monadLift_self, openReadOnly, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

/-- The actual cross-crate implementation allocates two distinct capabilities.
Both initially observe the same inode, with independent zero offsets. -/
theorem distinct_handles (state : State) (firstScript secondScript rest : Term)
    (visible : state.visible.size ≤ limit) (durable : state.durable.size ≤ limit) :
    open_pair path
      (initial state (choice true 0 firstScript (choice true 0 secondScript rest))) =
      (.ok (.Ok (⟨2⟩, ⟨3⟩)), openedPair state firstScript secondScript rest) := by
  simp only [open_pair, monadLift_self]
  rw [core_open_next state firstScript (choice true 0 secondScript rest) visible durable]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind]
  rw [core_open_again_next state firstScript secondScript rest visible durable]
  simp [NativeM.ok, Result.ok_apply]

/-- A failed first open allocates no handle and consumes only its OS outcome. -/
theorem core_open_error_next {α : Type} (state : State) (error : Nat) (rest : Term)
    (next : core.result.Result NativeFile NativeIoError → NativeM α) :
    (io_core.open_readonly path >>= next) (initial state (choice false error .nil rest)) =
      next (.Err ⟨error⟩) (initial state rest) := by
  have poll : pollOpenReadOnly path (initial state (choice false error .nil rest)) =
      some (.ok (.Err ⟨error⟩), initial state rest) := by
    have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
    simp [pollOpenReadOnly, supportedOpenPath, path_bytes, valid_name, not_directory, initial, namespaceCell, nodeCell,
      namespaceState, namespaceSnapshot, namespaceTable, namespaceHistory,
      encodeNamespace, encodeNames, tablesEqual, namespaceEntry, List.eraseDups_cons, choice, openChoice, pathChoice,
      replaceNamespaceScript, namespaceTypeName, nonnegative]
  simp only [io_core.open_readonly, monadLift_self, openReadOnly, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

theorem open_error (state : State) (error : Nat) (rest : Term) :
    open_readonly path (initial state (choice false error .nil rest)) =
      (.ok (.Err ⟨error⟩), initial state rest) := by
  have returned := core_open_error_next state error rest Result.ok
  simpa [open_readonly, monadLift_self, Result.bind_ok, Result.ok_apply] using returned

/-- The actual `?` error branch propagates the error through standard FromResidual
without opening a second handle or consuming a second host outcome. -/
theorem pair_first_error (state : State) (error : Nat) (rest : Term) :
    open_pair path (initial state (choice false error .nil rest)) =
      (.ok (.Err ⟨error⟩), initial state rest) := by
  simp only [open_pair, monadLift_self]
  rw [core_open_error_next state error rest]
  simp [core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame, NativeM.monadLift_eq, NativeM.fromRust,
    NativeM.ok, Result.ok_bind, Result.ok_apply]

/-- Reading the first actual extracted handle preserves the second handle's
position and script while publishing updated inode contents to both handles. -/
theorem read_first_independent (state after : State) (firstScript secondScript rest : Term)
    (buffer updated : Slice U8) (reply : core.result.Result Usize NativeIoError)
    (visible : state.visible.size ≤ limit) (durable : state.durable.size ≤ limit)
    (afterVisible : after.visible.size ≤ limit) (afterDurable : after.durable.size ≤ limit)
    (ready : blocked {state with position := 0, script := firstScript} = false)
    (step : readStep {state with position := 0, script := firstScript} buffer =
      some (reply, after, updated)) :
    io_core.read_once ⟨2⟩ buffer (openedPair state firstScript secondScript rest) =
      (.ok (reply, ⟨2⟩, updated), store ⟨2⟩ after (openedPair state firstScript secondScript rest)) ∧
    lookup ⟨3⟩ (store ⟨2⟩ after (openedPair state firstScript secondScript rest)) =
      some {after with position := 0, script := secondScript} := by
  simp only [limit] at visible durable afterVisible afterDurable
  have before : lookup ⟨2⟩ (openedPair state firstScript secondScript rest) =
      some {state with position := 0, script := firstScript} := by
    simp [lookup, sharedLookup, getHandle, decodeHandle, openedPair, namespaceCell,
      nodeCell, inode, decode, encode, encodeHandle, not_lt.mpr visible,
      not_lt.mpr durable, handleTypeName, inodeTypeName, namespaceTypeName, typeName, limit]
  constructor
  · have poll : pollRead ⟨2⟩ buffer (openedPair state firstScript secondScript rest) =
        some (.ok (reply, ⟨2⟩, updated), store ⟨2⟩ after (openedPair state firstScript secondScript rest)) := by
      simp [pollRead, before, ready, step]
    simp only [io_core.read_once, monadLift_self, NativeFile.read]
    rw [Result.wait_ready_apply _ _ _ _ _ poll]
    simp [Result.ok_apply]
  · simp [store, lookup, sharedStore, sharedLookup, getHandle, decodeHandle,
      openedPair, namespaceCell, nodeCell, inode, decode, encode, encodeHandle,
      not_lt.mpr afterVisible, not_lt.mpr afterDurable,
      handleTypeName, inodeTypeName, namespaceTypeName, typeName, limit]

theorem core_open_again_error_next {α : Type} (state : State) (firstScript : Term)
    (error : Nat) (rest : Term)
    (next : core.result.Result NativeFile NativeIoError → NativeM α) :
    (io_core.open_readonly path >>= next)
      (opened state firstScript (choice false error .nil rest)) =
      next (.Err ⟨error⟩) (opened state firstScript rest) := by
  have poll : pollOpenReadOnly path
      (opened state firstScript (choice false error .nil rest)) =
      some (.ok (.Err ⟨error⟩), opened state firstScript rest) := by
    have nonnegative : ¬ (error : Int) < 0 := not_lt.mpr (Int.natCast_nonneg error)
    simp [pollOpenReadOnly, supportedOpenPath, path_bytes, valid_name, not_directory, opened, namespaceCell, nodeCell,
      namespaceState, namespaceSnapshot, namespaceTable, namespaceHistory,
      encodeNamespace, encodeNames, tablesEqual, namespaceEntry, List.eraseDups_cons, choice, openChoice, pathChoice,
      replaceNamespaceScript, namespaceTypeName, handleTypeName, nonnegative]
  simp only [io_core.open_readonly, monadLift_self, openReadOnly, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.ok_bind]

/-- Failure of the second OS open runs the actual Rust cleanup of the first
handle. The admitted close choice may persist bytes, but never implies fsync. -/
theorem pair_second_error (state after : State) (firstScript : Term) (error : Nat) (rest : Term)
    (visible : state.visible.size ≤ limit) (durable : state.durable.size ≤ limit)
    (ready : blocked {state with position := 0, script := firstScript} = false)
    (step : closeStep {state with position := 0, script := firstScript} = some after) :
    open_pair path
      (initial state (choice true 0 firstScript (choice false error .nil rest))) =
      (.ok (.Err ⟨error⟩), retire ⟨2⟩ after (opened state firstScript rest)) := by
  have before : lookup ⟨2⟩ (opened state firstScript rest) =
      some {state with position := 0, script := firstScript} := by
    simp only [limit] at visible durable
    simp [lookup, sharedLookup, getHandle, decodeHandle, opened, namespaceCell,
      nodeCell, inode, decode, encode, encodeHandle, not_lt.mpr visible,
      not_lt.mpr durable, handleTypeName, inodeTypeName, namespaceTypeName, typeName, limit]
  have closeReady : pollClose ⟨2⟩ (opened state firstScript rest) =
      some (.ok (), retire ⟨2⟩ after (opened state firstScript rest)) := by
    simp [pollClose, before, ready, step]
  simp only [open_pair, monadLift_self]
  rw [core_open_next state firstScript (choice false error .nil rest) visible durable]
  simp only [core.result.Result.Insts.CoreOpsTry.branch, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind]
  rw [core_open_again_error_next state firstScript error rest]
  simp only [NativeOwnedDrop.drop, close, Result.wait_bind]
  rw [Result.wait_ready_apply _ _ _ _ _ closeReady]
  simp [NativeM.ok, Result.ok_bind, Result.ok_apply]

/-- Unsupported path forms are verification exhaustion, never an invented OS
error or successful Rust result. No environmental choice can bypass this bound. -/
theorem unsupported_path (input : Str) (env : Environment)
    (rejected : supportedOpenPath (bytes input) = false) :
    open_readonly input env = (.error .exhausted, env) := by
  have poll : pollOpenReadOnly input env = some (.error .exhausted, env) := by
    simp [pollOpenReadOnly, rejected]
  simp only [open_readonly, io_core.open_readonly, monadLift_self, openReadOnly]
  rw [Result.wait_ready_apply _ _ _ _ _ poll]
  simp [Result.error_apply]

end Open.Properties
