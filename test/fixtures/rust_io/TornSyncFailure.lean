module
public import Record.NamedJournalCrash
public import Record.FallibleReopen
import Mathlib.Tactic.FinCases
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.TornSyncFailure
open NativeFile
open Record.FallibleReopen (journalName contents call environment)
open Record.FallibleReopen (openScript)
open Record.NamedJournalCrash (inodeIds namedJournal)
open scoped Lynx.NativeArithmetic

@[expose] def zeros (count : Nat) : ByteArray := ⟨_root_.Array.replicate count 0⟩

@[expose] def choose (op : String) (ok : Bool) (count : Nat) (mask : ByteArray) (rest : Term) : Term :=
  .cons (.tuple #[.atom op, .atom (if ok then "ok" else "error"), .integer count, .bitstring mask 0]) rest

@[expose] def ioScript (tailLength error syncTail closeTail : Nat) (closeSucceeds : Bool) : Term :=
  let written := 8 + tailLength
  let currentMask := zeros written
  let close := choose "close" closeSucceeds (if closeSucceeds then 0 else 5) (zeros (8 + closeTail)) .nil
  let failure := choose "sync_all" false error (zeros (8 + syncTail)) close
  let eof := choose "read" true 0 currentMask (choose "set_len" true 0 currentMask failure)
  choose "seek" true 0 currentMask
    ((List.range written).foldr (fun _ => choose "read" true 1 currentMask) eof)

@[expose] def withTail (left : Bool) (tail : List UInt8) : ByteArray :=
  ⟨(contents left).data ++ tail.toArray⟩

@[expose] def boot (counter : Nat) (left : Bool) (tail : List UInt8)
    (syncTail closeTail : Nat) (closeSucceeds : Bool) : Environment :=
  let data := withTail left tail
  let names := namedJournal journalName
  let error := counter + 1
  { nativeRefCounter := error,
    nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource],
    nativeHeap := [
      (0, namespaceTypeName, encodeNamespace ⟨names, names, [],
        openScript true 0 (ioScript tail.length error syncTail closeTail closeSucceeds) .nil⟩),
      (1, inodeTypeName, encode ⟨data, data, 0, .nil⟩),
      (error, NativeIoError.typeName, .atom "live")] }

@[expose] def preserves (left : Bool) (data : ByteArray) : Bool :=
  8 ≤ data.size && data.size < 12 && (List.range 8).all (fun i => data[i]! == (contents left)[i]!)

@[expose] def rejected (counter : Nat) (left : Bool) (tailLength closeTail : Nat)
    (last : Concurrent.Config Term) : Bool :=
  let env := environment last
  match last.outcome, inode 1 env, namespaceSnapshot env,
      getHandle ⟨counter + 2⟩ closedHandleTypeName env with
  | .error (.error (.atom "journal_io")), some file, some table, some descriptor =>
    let names := namedJournal journalName
    file.visible.data == (contents left).data && preserves left file.durable &&
    file.durable.size == 8 + closeTail &&
    tablesEqual table.names names && tablesEqual table.committed names &&
    table.pending.isEmpty && table.script == .nil &&
    env.nativeRefCounter == counter + 2 && env.nativeHeap.length == 3 && inodeIds env == [1] &&
    descriptor.inode == 1 && descriptor.position == 8 + tailLength && descriptor.script == .nil &&
    !env.nativeHeap.any (fun entry => entry.1 == counter + 1)
  | _, _, _, _ => false

theorem tail_forms (tail : List UInt8) (short : tail.length < 4) :
    tail = [] ∨ (∃ a, tail = [a]) ∨ (∃ a b, tail = [a,b]) ∨ (∃ a b c, tail = [a,b,c]) := by
  cases tail with
  | nil => exact .inl rfl
  | cons first rest =>
    cases rest with
    | nil => exact .inr (.inl ⟨first, rfl⟩)
    | cons second rest =>
      cases rest with
      | nil => exact .inr (.inr (.inl ⟨first, second, rfl⟩))
      | cons third rest =>
        cases rest with
        | nil => exact .inr (.inr (.inr ⟨first, second, third, rfl⟩))
        | cons fourth rest =>
          simp only [List.length_cons] at short
          omega

set_option maxRecDepth 8192 in
set_option maxHeartbeats 128000000 in
/-- Failed synchronization after truncating an arbitrary short tail releases the
actual descriptor and error capability. Each admitted all-old length choice at
failed sync and close preserves both acknowledged records. -/
theorem failed_sync_preserves_acknowledgements (counter : Nat) (left : Bool)
    (tail : List UInt8) (short : tail.length < 4) (syncTail closeTail : Fin 4)
    (syncBound : syncTail.val ≤ tail.length) (closeBound : closeTail.val ≤ syncTail.val)
    (closeSucceeds : Bool) (positive : 1 ≤ counter) (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (rejected counter left tail.length closeTail.val) 64
      (.start (boot counter left tail syncTail.val closeTail.val closeSucceeds)
        (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    fin_cases syncTail <;> fin_cases closeTail <;>
    simp only [List.length_nil, List.length_cons] at syncBound closeBound <;>
    try contradiction
  all_goals first | omega | cases left <;> cases closeSucceeds <;> cbv

@[expose] def failedSyncBoot : Environment := boot 1 true [99,0] 2 1 false

end Record.TornSyncFailure
