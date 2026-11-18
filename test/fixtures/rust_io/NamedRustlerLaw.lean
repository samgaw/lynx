module
public import Record.NamedRustlerAdapterProof
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.NamedRustlerLaw
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.NamedRustlerRepair (nameBytes boot)
open Record.NamedJournalCrash (namedJournal inodeIds)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.RepeatedRepairProperties (repairScript)

@[expose] def records : List U16 := [7#u16, 129#u16, 1027#u16]
@[expose] def complete : ByteArray := disk (logBytes records)
@[expose] def torn : ByteArray := disk (logBytes records ++ [222#u8, 21#u8])
@[expose] def repairBoot : Environment := boot 1 torn (repairScript torn .nil) .nil

@[expose] def rawAccepted (last : Concurrent.Config Record.NamedRustlerAdapterProof.Reply) : Bool :=
  match last.outcome with
  | .ok (.Ok owner) => owner.id == 4 && owner.token == 5
  | _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 64000000 in
theorem concrete_raw_result (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost rawAccepted 96 (.start repairBoot (__TRY_REOPEN__ 5#u32) elapsed) = true := by
  set_option cbv.maxSteps 32000000 in cbv

@[expose] def accepted (last : Concurrent.Config Term) : Bool :=
  let env := match last with
    | .start env .. => env
    | .running state .. => state.nativeView []
  match last.outcome, inode 1 env, getHandle ⟨2⟩ writableHandleTypeName env, namespaceSnapshot env with
  | .ok (.atom "true"), some file, some descriptor, some table =>
    let payload : shared_log.LogResource := ⟨⟨3⟩⟩
    file.visible.data == complete.data && file.durable.data == complete.data &&
    descriptor.inode == 1 && descriptor.position == torn.size && descriptor.script == .nil &&
    table.pending.isEmpty && table.script == .nil &&
    tablesEqual table.names (namedJournal nameBytes) && tablesEqual table.committed (namedJournal nameBytes) &&
    inodeIds env == [1] && env.nativeRefCounter == 7 &&
    (NativeResourceArc.vmCells payload 4 6 7).all env.nativeHeap.contains &&
    !env.nativeHeap.any (fun cell => cell.1 == 5)
  | _, _, _, _ => false

theorem law_outcome (last : Concurrent.Config Term) (good : accepted last = true) :
    last.outcome = .ok Term.true := by
  unfold accepted at good
  dsimp only at good
  split at good
  · assumption
  · contradiction

end Record.NamedRustlerLaw
