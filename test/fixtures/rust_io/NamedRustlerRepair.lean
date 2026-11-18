module
public import Record.NamedRepairAcknowledgement
public import Record.NamedJournalCrash
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol

namespace Record.NamedRustlerRepair
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FileView (namedWorld NamedSeparated named_inode named_render named_separated inodeCell handleCell)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.RepairCrashProperties (LogImage)
open Record.ResizeProperties (Admitted)
open Record.NamedJournalCrash (namedJournal captured_journal inodeIds)

@[expose] def nameBytes : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩

private theorem actual_path : bytes (toStr "journal") = nameBytes := by cbv
private theorem path_valid : supportedPath nameBytes = true := by decide

@[expose] def openScript (choices rest : Term) : Term :=
  .cons (.tuple #[.atom "open", .bitstring nameBytes 0, .atom "ok", .integer 0, choices]) rest

@[expose] def namespaceCell (script : Term) : Nat × String × Term :=
  let names := [(nameBytes, 1)]
  (0, namespaceTypeName, encodeNamespace ⟨names, names, [], script⟩)

@[expose] def openingState (data : ByteArray) (choices : Term) : State :=
  ⟨data, data, 0, choices⟩

@[expose] def boot (counter : Nat) (data : ByteArray) (choices rest : Term) : Environment := {
  nativeRefCounter := counter
  nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource]
  nativeHeap := [namespaceCell (openScript choices rest),
    inodeCell 1 (openingState data choices)] }

@[expose] def opened (counter : Nat) (data : ByteArray) (choices rest : Term) : Environment :=
  namedWorld 1 (boot counter data choices rest) ⟨counter + 1⟩
    (openingState data choices) [namespaceCell rest]

theorem opened_frame (counter : Nat) (rest : Term) (positive : 1 ≤ counter) :
    NamedSeparated 1 ⟨counter + 1⟩ [namespaceCell rest] := by
  simp [NamedSeparated, Record.Properties.Separate, namespaceCell]
  omega

set_option maxRecDepth 8192 in
private theorem poll_success (counter : Nat) (data : ByteArray) (choices rest : Term)
    (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit) :
    pollOpenReadWrite (toStr "journal") (boot counter data choices rest) =
      some (.ok (.Ok ⟨counter + 1⟩), opened counter data choices rest) := by
  have nonzero : counter ≠ 0 := by omega
  simp [pollOpenReadWrite, actual_path, path_valid, boot, opened, openingState, namedWorld,
    namespaceCell, namespaceState, namespaceSnapshot, namespaceTable, namespaceHistory,
    encodeNamespace, encodeNames, tablesEqual, namespaceEntry, List.eraseDups_cons,
    openScript, openChoice, pathChoice, inode, decode, encode, inodeCell, handleCell, encodeHandle,
    not_lt.mpr positive, not_lt.mpr bounded, replaceNamespaceScript, nonzero]

/-- The open uses an authenticated ready poll of the compiled Rust caller. -/
theorem open_existing_prefix (counter : Nat) (data : ByteArray) (choices rest : Term)
    (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit) :
    Result.ReadyPrefix (io_protocol.open_readwrite (toStr "journal"))
      (boot counter data choices rest) (.ok (.Ok ⟨counter + 1⟩))
      (opened counter data choices rest) := by
  simp only [io_protocol.open_readwrite, io_core.open_readwrite, NativeFile.OpenOptions.read,
    NativeFile.OpenOptions.write, NativeFile.OpenOptions.openFile, monadLift_self, openReadWrite, ite_true]
  exact .wait _ _ _ _ _ _ _ (poll_success counter data choices rest positive bounded) (.refl _ _)

theorem open_existing (counter : Nat) (data : ByteArray) (choices rest : Term)
    (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit) :
    io_protocol.open_readwrite (toStr "journal") (boot counter data choices rest) =
      (.ok (.Ok ⟨counter + 1⟩), opened counter data choices rest) := by
  simpa only [Result.ok_apply] using (open_existing_prefix counter data choices rest positive bounded).run []

@[expose] def initialized (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) : Environment :=
  let world := namedWorld 1 (boot counter data choices rest) ⟨counter + 1⟩ after [namespaceCell rest]
  let resource : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
  {world with nativeRefCounter := counter + 4, nativeHeap := [
    (counter + 4, NativeResourceArc.handleType shared_log.LogResource, .nativeReference (counter + 3)),
    (counter + 3, NativeResourceArc.typeName shared_log.LogResource,
      .tuple #[.integer 1, NativeCodec.encode resource]),
    (counter + 2, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (⟨counter + 1⟩ : NativeFile)])
  ] ++ world.nativeHeap}

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem allocate_resource (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) (positive : 1 ≤ counter) :
    (do
      let mutex ← NativeMutex.new (⟨counter + 1⟩ : NativeFile)
      let owner ← NativeResourceArc.newOwned (⟨mutex⟩ : shared_log.LogResource)
      Result.ok (.Ok (some owner) :
        core.result.Result (Option (NativeResourceArc shared_log.LogResource)) NativeIoError))
     (namedWorld 1 (boot counter data choices rest) ⟨counter + 1⟩ after [namespaceCell rest]) =
      (.ok (.Ok (some ⟨counter + 3, counter + 4⟩)), initialized counter data choices rest after) := by
  have above : max counter (max (counter + 1) 1) = counter + 1 := by omega
  have distinct : ∀ n, counter + 1 < n → n ≠ 1 := by omega
  have low : ∀ n, counter + 1 < n → 1 ≠ n := by omega
  simp [initialized, namedWorld, boot, namespaceCell, inodeCell, handleCell, above,
    NativeMutex.new, NativeM.allocate, NativeResourceArc.newOwned, NativeResourceArc.new,
    distinct, low, Nat.add_assoc, Result.ok_apply, Result.ofExcept, Result.nativeGet_bind,
    Result.nativeGet_continuation_apply]

set_option maxRecDepth 8192 in
private theorem reopen_result (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maxRecords : Usize) (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit)
    (image : LogImage values data) (owner : NativeResourceArc shared_log.LogResource) (world : Environment)
    (trace : Result.ReadyPrefix (shared_log.reopen maxRecords)
      (boot counter data choices rest) (.ok (.Ok (some owner))) world) :
    ∃ after, owner = ⟨counter + 3, counter + 4⟩ ∧
      world = initialized counter data choices rest after ∧
      after.visible = disk (logBytes values) ∧ after.durable = disk (logBytes values) ∧ Admitted after := by
  simp only [shared_log.reopen, monadLift_self] at trace
  obtain ⟨reply, readyWorld, openedTrace, trace⟩ := trace.bind_returns
  have didOpen := openedTrace.run []
  simp only [Result.ok_apply, open_existing counter data choices rest positive bounded,
    Prod.mk.injEq, Outcome.ok.injEq] at didOpen
  obtain ⟨rfl, rfl⟩ := didOpen
  simp only [core.result.Result.Insts.CoreOpsTry.branch, NativeM.monadLift_eq,
    NativeM.fromRust_ok, Result.ok_bind] at trace
  obtain ⟨⟨reply, file⟩, repairedWorld, repairedTrace, trace⟩ := trace.bind_returns
  cases reply with
  | Err error =>
    simp only [NativeM.ok, Result.ok_bind] at trace
    obtain ⟨_, _, _, trace⟩ := trace.bind_returns
    cases trace
  | Ok result =>
    cases result with
    | none =>
      simp only [NativeM.ok, Result.ok_bind] at trace
      obtain ⟨_, _, _, trace⟩ := trace.bind_returns
      cases trace
    | some records =>
      have separate := (named_separated 1 ⟨counter + 1⟩ [namespaceCell rest]).mpr (opened_frame counter rest positive)
      have admitted : Admitted (openingState data choices) := ⟨bounded, bounded, Nat.zero_le _⟩
      unfold opened at repairedTrace
      rw [← named_render] at repairedTrace
      obtain ⟨sameFile, _, after, repairedEq, visible, durable, admittedAfter⟩ :=
        Record.RepairAcknowledgement.repair_returns (view := Record.FileView.named 1)
          ⟨counter + 1⟩ (boot counter data choices rest) [namespaceCell rest]
          (openingState data choices) values maxRecords records file repairedWorld separate admitted rfl image repairedTrace
      subst file
      rw [named_render] at repairedEq
      subst repairedWorld
      have finished := trace.run []
      simp only [Result.ok_apply, NativeM.ok] at finished
      have returned := (allocate_resource counter data choices rest after positive).symm.trans finished
      simp only [Prod.mk.injEq, Outcome.ok.injEq, core.result.Result.Ok.injEq, Option.some.injEq] at returned
      obtain ⟨rfl, rfl⟩ := returned
      exact ⟨after, rfl, rfl, visible, durable, admittedAfter⟩

set_option maxRecDepth 8192 in
/-- Every successful return of the actual compiled typed NIF body is linked to
the exact successful scan/resize/sync trace and resource allocation. The loose
file bytes and admitted host script are arbitrary. -/
theorem arbitrary_repair_result (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maxRecords : U32) (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit)
    (image : LogImage values data) (owner : NativeResourceArc shared_log.LogResource) (world : Environment)
    (trace : Result.ReadyPrefix (__TRY_REOPEN__ maxRecords)
      (boot counter data choices rest) (.ok (.Ok owner)) world) :
    ∃ after, owner = ⟨counter + 3, counter + 4⟩ ∧
      world = initialized counter data choices rest after ∧
      after.visible = disk (logBytes values) ∧ after.durable = disk (logBytes values) ∧ Admitted after := by
  simp only [__TRY_REOPEN__, monadLift_self, NativeM.lift, Result.ok_bind] at trace
  obtain ⟨reply, middle, raw, finish⟩ := trace.bind_returns
  cases reply with
  | Err error =>
    simp only [NativeM.ok] at finish
    obtain ⟨_, _, _, finish⟩ := finish.bind_returns
    cases finish
  | Ok result =>
    cases result with
    | none => simp only [NativeM.ok] at finish; cases finish
    | some returned =>
      simp only [NativeM.ok] at finish
      cases finish
      exact reopen_result counter data choices rest values _ positive bounded image owner world raw

set_option maxRecDepth 8192 in
private theorem initialized_inode (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) (positive : 1 ≤ counter) (valid : Admitted after) :
    inode 1 (initialized counter data choices rest after) =
      some {after with position := 0, script := .nil} := by
  have one : 1 ≤ counter + 4 := by omega
  have nonzero : counter ≠ 0 := by omega
  have mutex : 1 ≠ counter + 2 := by omega
  have resource : 1 ≠ counter + 3 := by omega
  have owner : 1 ≠ counter + 4 := by omega
  have validNode : Admitted {after with position := 0, script := .nil} :=
    ⟨valid.1, valid.2.1, Nat.zero_le _⟩
  simp [initialized, namedWorld, boot, handleCell, namespaceCell, inodeCell, inode,
    ne_comm.mp mutex, ne_comm.mp resource, ne_comm.mp owner, not_lt.mpr one,
    List.filter_append, List.filter_cons, nonzero,
    Record.ResizeProperties.decode_admitted _ validNode]

set_option maxRecDepth 8192 in
private theorem initialized_namespace (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) :
    namespaceSnapshot (initialized counter data choices rest after) =
      some ⟨namedJournal nameBytes, namedJournal nameBytes, [], rest⟩ := by
  have zero : ∀ n, 0 < n → counter + n ≠ 0 := by omega
  have supported := path_valid
  simp [initialized, namedWorld, boot, handleCell, namespaceCell, inodeCell, namespaceSnapshot,
    encodeNamespace, encodeNames, namespaceTable, namespaceHistory, namespaceEntry, List.eraseDups_cons,
    tablesEqual, namedJournal, supported, zero]

private theorem initialized_ids (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) : inodeIds (initialized counter data choices rest after) = [1] := by
  have owner : (NativeResourceArc.handleType shared_log.LogResource == inodeTypeName) = false := by cbv
  have resource : (NativeResourceArc.typeName shared_log.LogResource == inodeTypeName) = false := by cbv
  have mutex : (NativeMutex.typeName NativeFile == inodeTypeName) = false := by cbv
  simp only [initialized, namedWorld, boot, inodeIds, handleCell, inodeCell, namespaceCell,
    List.cons_append, List.nil_append, List.filter_cons, owner, resource, mutex]
  rfl

/-- A success reported by the actual typed Rustler body leaves the complete
journal image synchronized. Every admitted power loss captures those same
bytes, even when the original image and partial-record tail were arbitrary. -/
theorem arbitrary_repair_persists (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maxRecords : U32) (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit)
    (image : LogImage values data) (owner : NativeResourceArc shared_log.LogResource) (world : Environment)
    (trace : Result.ReadyPrefix (__TRY_REOPEN__ maxRecords)
      (boot counter data choices rest) (.ok (.Ok owner)) world)
    (chosen : Names) (masks : List (Nat × ByteArray)) (captured : FilesystemImage)
    (crash : filesystemCrashImage chosen masks world = some captured) :
    captured = ⟨namedJournal nameBytes, [(1, disk (logBytes values))], counter + 4⟩ := by
  obtain ⟨after, _, rfl, visible, durable, valid⟩ :=
    arbitrary_repair_result counter data choices rest values maxRecords positive bounded image owner world trace
  obtain ⟨mask, stored, admitted, storedEq⟩ :=
    captured_journal nameBytes _ {after with position := 0, script := .nil} rest
      (initialized_namespace counter data choices rest after)
      (initialized_ids counter data choices rest after)
      (initialized_inode counter data choices rest after positive valid)
      chosen masks captured crash
  simp only [visible, durable] at admitted
  rw [storedEq, NativeFile.persist_same _ _ _ admitted]
  rfl

end Record.NamedRustlerRepair
