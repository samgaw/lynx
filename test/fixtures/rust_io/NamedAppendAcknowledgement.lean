module
public import Record.AppendAcknowledgementWitness
public import Record.NamedJournalCrash

public section

open Aeneas Aeneas.Std Lynx io_protocol

namespace Record.NamedAppendAcknowledgement
open NativeFile
open Record.FileView (namedWorld NamedSeparated named_render named_separated named_inode inodeCell handleCell)
open Record.NamedJournalCrash (namedJournal captured_journal inodeIds)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.RepairCrashProperties (LogImage)
open Record.ResizeProperties (Admitted)
open Record.RepairAppendAcknowledgement (repair_append_run_acknowledges snapshot)

@[expose] def journalCell (path : ByteArray) (choices : Term) : Nat × String × Term :=
  let names := namedJournal path
  (0, namespaceTypeName, encodeNamespace ⟨names, names, [], choices⟩)

set_option maxRecDepth 8192 in
/-- A true return from the extracted repair/append caller on a named writable
descriptor synchronizes the old records and the new one. Every admitted
filesystem crash retains that exact byte image under the same path and inode. -/
theorem named_append_persists (path : ByteArray) (supported : supportedPath path = true)
    (env : Environment) (file : NativeFile) (before : State) (choices : Term) (values : List U16)
    (maximum : Usize) (value : U16) (separate : NamedSeparated 1 file [journalCell path choices])
    (valid : Admitted before) (stable : before.durable = before.visible) (image : LogImage values before.visible)
    (elapsed : PID → Nat → Nat) (events : List Concurrent.Event)
    (last : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile)) (returned : NativeFile)
    (run : Concurrent.Run (.start (namedWorld 1 env file before [journalCell path choices])
      (repair_and_append file maximum value) elapsed) events last)
    (terminal : Concurrent.Terminal last (.ok (.Ok true, returned))) (chosen : Names)
    (masks : List (Nat × ByteArray)) (crash : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (snapshot env.currentPid last) = some crash) :
    returned = file ∧ crash = ⟨namedJournal path, [(1, disk (logBytes (values ++ [value])))],
      max env.nativeRefCounter (max file.id 1)⟩ := by
  obtain ⟨same, after, ended, visible, durable, admitted⟩ :=
    repair_append_run_acknowledges (view := Record.FileView.named 1) file value env
      [journalCell path choices] before values maximum returned ((named_separated 1 _ _).mpr separate)
      valid stable image elapsed events last (by simpa only [named_render] using run) terminal
  have positive := separate.1
  rw [ended] at captured
  simp only [snapshot, named_render] at captured
  let world := namedWorld 1 env file after [journalCell path choices]
  have namespaceEq : namespaceSnapshot world =
      some ⟨namedJournal path, namedJournal path, [], choices⟩ := by
    simp [world, namedWorld, handleCell, inodeCell, journalCell, namespaceSnapshot,
      encodeNamespace, encodeNames, namespaceTable, namespaceHistory, namespaceEntry,
      List.eraseDups_cons, tablesEqual, namedJournal, supported, positive]
  have ids : inodeIds world = [1] := by rfl
  have inodeEq : inode 1 world = some {after with position := 0, script := .nil} :=
    named_inode 1 env file after [journalCell path choices] separate admitted
  obtain ⟨mask, bytes, accepted, shape⟩ := captured_journal path world
    {after with position := 0, script := .nil} choices namespaceEq ids inodeEq chosen masks crash captured
  have persisted : bytes = disk (logBytes (values ++ [value])) := by
    simp only [visible, durable] at accepted
    exact NativeFile.persist_same _ _ _ accepted
  exact ⟨same, by rw [shape, persisted]; rfl⟩

open Record.AppendAcknowledgementWitness (original complete torn appendScript)
open Record.RepeatedRepairProperties (repairScript)

@[expose] def observed (config : Concurrent.Config (core.result.Result Bool NativeIoError × NativeFile)) : Bool :=
  let env := snapshot [] config
  match config.outcome, lookup ⟨2⟩ env, inode 1 env with
  | .ok (.Ok true, returned), some file, some node =>
    returned.id == 2 && file.position == 8 && file.script == .nil &&
    file.visible == complete && file.durable == complete &&
    node.visible == complete && node.durable == complete
  | _, _, _ => false

set_option maxRecDepth 8192 in
/-- A completed Rust repair and append synchronizes both views of the named file. -/
theorem named_torn_append : Concurrent.checkPost observed 256
    (.start (namedWorld 1 {} ⟨2⟩
      ⟨torn, torn, 3, repairScript torn (appendScript original 4 false)⟩
      [journalCell ⟨#[106,111,117,114,110,97,108]⟩ .nil])
      (repair_and_append ⟨2⟩ 4#usize 19#u16)) = true := by
  cbv

end Record.NamedAppendAcknowledgement
