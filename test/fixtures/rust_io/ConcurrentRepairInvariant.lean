module
public import Record.LockedRepairProperties
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.ConcurrentRepairInvariant
open NativeFile Record.Properties Record.CrashProperties Record.LogProperties
  Record.ResizeProperties Record.RepairCrashProperties Record.RecoveryScanInvariant
  Record.RepeatedRepairProperties Record.LockedProperties

@[expose] def complete : ByteArray := disk (logBytes [13#u16])
@[expose] def torn : ByteArray := disk (logBytes [13#u16] ++ [7#u8])
@[expose] def fileScript : Term := repairScript torn (repairScript complete .nil)
@[expose] def initial : Environment :=
  fileEnv {} ⟨2⟩ ⟨torn, torn, 0, fileScript⟩
    [(1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2])]

/-- Observe the actual Rust result without accepting an error, limit return or
wrong recovered list as a successful repair. -/
@[expose] def repaired : Result Term := do
  let reply ← locked_repair ⟨1⟩ 3#usize
  .ok (match reply with
    | .Ok (some values) => Rustler.encodeBool (values.val == [13#u16])
    | _ => Term.false)

/-- Both actual Rust calls must acknowledge the expected records. The child's
reply is explicitly collected rather than discarded by process completion. -/
@[expose] def callers : Result Term :=
  Result.schedule {} (do
    let reply ← repaired
    Result.send [] reply (.ok .nil)) fun _ => do
      let first ← repaired
      Result.receive .infinity (fun _ value => some value) fun second =>
        .ok (if first == Term.true && second == some Term.true then Term.true else Term.false)

@[expose] def snapshot : Concurrent.Config Term → Environment
  | .start env .. => env
  | .running state .. => state.nativeView []

@[expose] def retained (config : Concurrent.Config Term) : Bool :=
  match NativeFile.lookup ⟨2⟩ (snapshot config) with
  | some file => (file.visible == torn || file.visible == complete) &&
      (file.durable == torn || file.durable == complete)
  | none => false

@[expose] def accepted (config : Concurrent.Config Term) : Bool :=
  match config.outcome, NativeFile.lookup ⟨2⟩ (snapshot config) with
  | .ok (.atom "true"), some file => file.visible == complete && file.durable == complete &&
      (snapshot config).nativeHeap.contains (1, NativeMutex.typeName NativeFile,
        .tuple #[.atom "unlocked", .atom "unpoisoned", .nativeReference 2])
  | _, _ => false


@[expose] def safe (config : Concurrent.Config Term) : Bool :=
  retained config && (!config.successors.isEmpty || accepted config)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 128000000 in
/-- Every raw prefix retains the acknowledged record; every terminal state
acknowledges both repairs and has the exact synchronized image and free mutex. -/
theorem prefixes_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant safe 192 (.start initial callers elapsed) = true := by
  set_option cbv.maxSteps 64000000 in cbv

end Record.ConcurrentRepairInvariant
