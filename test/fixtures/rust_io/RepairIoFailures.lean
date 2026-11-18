module
public import Record.FallibleReopen
import Mathlib.Tactic.FinCases
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Record.RepairIoFailures
open NativeFile
open Record.FallibleReopen (journalName contents choice readBytes openScript call environment)
open scoped Lynx.NativeArithmetic

inductive FailedOperation where
  | seek
  | read (position : Fin 9)
  | resize
  | sync

@[expose] def offset : FailedOperation → Nat
  | .seek => 0
  | .read position => position.val
  | .resize | .sync => 8

@[expose] def failedScript (operation : FailedOperation) (error : Nat) (closeSucceeds : Bool) : Term :=
  let close := choice "close" closeSucceeds (if closeSucceeds then 0 else 5) .nil
  let beforeResize := fun rest => choice "seek" true 0 (readBytes 8 (choice "read" true 0 rest))
  match operation with
  | .seek => choice "seek" false error close
  | .read position => choice "seek" true 0 (readBytes position.val (choice "read" false error close))
  | .resize => beforeResize (choice "set_len" false error close)
  | .sync => beforeResize (choice "set_len" true 0 (choice "sync_all" false error close))

@[expose] def boot (counter : Nat) (left closeSucceeds : Bool) (operation : FailedOperation) : Environment :=
  let data := contents left
  let names := [(journalName, 1)]
  let error := counter + 1
  { nativeRefCounter := error,
    nativeResourceTypes := [NativeResourceArc.typeName shared_log.LogResource],
    nativeHeap := [
      (0, namespaceTypeName, encodeNamespace ⟨names, names, [],
        openScript true 0 (failedScript operation error closeSucceeds) .nil⟩),
      (1, inodeTypeName, encode ⟨data, data, 0, .nil⟩),
      (error, NativeIoError.typeName, .atom "live")] }

@[expose] def rejected (counter : Nat) (left : Bool) (operation : FailedOperation)
    (last : Concurrent.Config Term) : Bool :=
  let env := environment last
  match last.outcome, inode 1 env, namespaceSnapshot env,
      getHandle ⟨counter + 2⟩ closedHandleTypeName env with
  | .error (.error (.atom "journal_io")), some file, some table, some descriptor =>
    let names := [(journalName, 1)]
    file.visible.data == (contents left).data && file.durable.data == (contents left).data &&
    tablesEqual table.names names && tablesEqual table.committed names &&
    table.pending.isEmpty && table.script == .nil &&
    env.nativeRefCounter == counter + 2 && env.nativeHeap.length == 3 &&
    descriptor.inode == 1 && descriptor.position == offset operation && descriptor.script == .nil &&
    !env.nativeHeap.any (fun entry => entry.1 == counter + 1)
  | _, _, _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 96000000 in
/-- For complete synchronized journals, seek, read, resize and sync failures are
reported as the typed I/O error. The rejected call consumes the admitted error
capability and closes the actual descriptor, with both recorded images intact. -/
theorem repair_failure_consumes_owners (counter : Nat) (left closeSucceeds : Bool)
    (operation : FailedOperation) (positive : 1 ≤ counter) (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (rejected counter left operation) 64
      (.start (boot counter left closeSucceeds operation)
        (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  cases operation with
  | seek => cases left <;> cases closeSucceeds <;> cbv
  | read position => fin_cases position <;> cases left <;> cases closeSucceeds <;> cbv
  | resize => cases left <;> cases closeSucceeds <;> cbv
  | sync => cases left <;> cases closeSucceeds <;> cbv

end Record.RepairIoFailures
