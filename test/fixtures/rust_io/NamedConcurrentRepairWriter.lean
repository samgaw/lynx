module
public import Record.ConcurrentRepairWriterInvariant
public import Record.FileView
public import Record.NamedJournalCrash

public section

open Aeneas Aeneas.Std Lynx io_protocol

namespace Record.NamedConcurrentRepairWriter
open NativeFile
open Record.FileView (namedWorld)
open Record.NamedJournalCrash (inodeIds)
open Record.RepairWriterObserver (ackTag acknowledgedAt callersAt)
open Record.ConcurrentRepairWriterInvariant (admittedBytes snapshot fileScript torn
  firstProtected secondProtected bothProtected)

@[expose] def journal : ByteArray := ⟨#[106,111,117,114,110,97,108]⟩

@[expose] def names : Names := [(journal, 1)]

@[expose] def free : Term :=
  .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2]

@[expose] def initial : Environment :=
  namedWorld 1 {nativeRefCounter := 4} ⟨2⟩ ⟨torn, torn, 0, fileScript⟩ [
    (0, namespaceTypeName, encodeNamespace ⟨names, names, [], .nil⟩),
    (3, NativeMutex.typeName NativeFile, free),
    (4, ackTag, .nil)]

@[expose] def acknowledged := acknowledgedAt 4

@[expose] def writers
    (append : NativeMutex NativeFile → Usize → U16 → NativeM (core.result.Result Bool NativeIoError)) :
    Result Term :=
  callersAt 4 (append ⟨3⟩ 4#usize 19#u16) (append ⟨3⟩ 4#usize 23#u16)

@[expose] def safe (config : Concurrent.Config Term) : Bool :=
  let env := snapshot config
  match inode 1 env, namespaceSnapshot env with
  | some file, some table =>
    tablesEqual table.names names && tablesEqual table.committed names &&
    table.pending.isEmpty && table.script == .nil &&
    inodeIds env == [1] && decide (1 ≤ env.nativeRefCounter) &&
    admittedBytes file.visible && admittedBytes file.durable &&
    (!acknowledged 19 env || firstProtected file.visible file.durable) &&
    (!acknowledged 23 env || secondProtected file.visible file.durable) &&
    (!(acknowledged 19 env && acknowledged 23 env) || bothProtected file.visible file.durable) &&
    (!config.successors.isEmpty ||
      ((match config.outcome with | .ok value => value == Term.true | _ => false) &&
        acknowledged 19 env && acknowledged 23 env &&
        bothProtected file.visible file.durable &&
        env.nativeHeap.contains (3, NativeMutex.typeName NativeFile, free)))
  | _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 256000000 in
theorem named_prefixes_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 256
      (.start initial (writers locked_repair_and_append) elapsed) = true := by
  set_option cbv.maxSteps 128000000 in cbv

end Record.NamedConcurrentRepairWriter
