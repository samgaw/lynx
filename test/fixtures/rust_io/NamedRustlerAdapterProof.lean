module
public import Record.NamedRustlerRepair

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.NamedRustlerAdapterProof
open NativeFile
open Record.NamedRustlerRepair (boot initialized arbitrary_repair_result namespaceCell)
open Record.FileView (handleCell inodeCell namedWorld)
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.RepairCrashProperties (LogImage)
open Record.ResizeProperties (Admitted)

abbrev Owner := NativeResourceArc shared_log.LogResource
abbrev Reply := core.result.Result Owner Rustler.DecoderError

@[expose] def pinned (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) : Environment :=
  let world := namedWorld 1 (boot counter data choices rest) ⟨counter + 1⟩ after [namespaceCell rest]
  let resource : shared_log.LogResource := ⟨⟨counter + 2⟩⟩
  { world with
    nativeRefCounter := counter + 6
    nativeHeap := NativeResourceArc.vmCells resource (counter + 3) (counter + 5) (counter + 6) ++
      [(counter + 2, NativeMutex.typeName NativeFile,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (⟨counter + 1⟩ : NativeFile)])] ++
      world.nativeHeap }

set_option maxRecDepth 8192 in
set_option maxHeartbeats 4000000 in
private theorem pin_resource (counter : Nat) (data : ByteArray) (choices rest : Term)
    (after : State) (positive : 1 ≤ counter) :
    (do
      let term ← NativeResourceArc.encode (⟨counter + 3, counter + 4⟩ : Owner)
      NativeOwnedDrop.drop (⟨counter + 3, counter + 4⟩ : Owner)
      Result.ok term) (initialized counter data choices rest after) =
        (.ok (.nativeReference (counter + 6)), pinned counter data choices rest after) := by
  have ne1 : ∀ k, 1 < k → counter + k ≠ 1 := by omega
  have rev : ∀ k, 1 < k → 1 ≠ counter + k := by omega
  simp [initialized, pinned, namedWorld, handleCell, inodeCell, boot, namespaceCell,
    NativeResourceArc.encode_eq, NativeOwnedDrop.drop, NativeResourceArc.releaseOwned,
    NativeResourceArc.clone, NativeResourceArc.ownership, NativeResourceArc.ownedState,
    NativeResourceArc.ownerState, NativeResourceArc.retiredState, NativeResourceArc.vmCells,
    NativeResourceArc.handleType, NativeResourceArc.typeName, NativeResourceArc.termType,
    NativeResourceArc.referenceLimit, NativeM.allocate, NativeCodec.roundtrip,
    NativeMutex.typeName, NativeCodec.typeName, namespaceTypeName, inodeTypeName, writableHandleTypeName,
    List.filter_append, List.map_append, Result.ofExcept, Result.ok_apply,
    Result.nativeGet_bind, Result.nativeGet_continuation_apply, Nat.add_assoc, ne1, rev]

set_option maxRecDepth 8192 in
/-- The modeled Rustler return path uses a separate VM pin and consumes
the temporary owner after an actual successful Rust call. -/
theorem arbitrary_repair_encodes (counter : Nat) (data : ByteArray) (choices rest : Term)
    (values : List U16) (maxRecords : U32) (positive : 1 ≤ counter) (bounded : data.size ≤ NativeFile.limit)
    (image : LogImage values data) (owner : Owner) (world : Environment)
    (trace : Result.ReadyPrefix (__TRY_REOPEN__ maxRecords)
      (boot counter data choices rest) (.ok (.Ok owner)) world) :
    ∃ after,
      (Rustler.withNativeResult (__TRY_REOPEN__ maxRecords) (fun owner => do
        let term ← NativeResourceArc.encode owner
        NativeOwnedDrop.drop owner
        Result.ok term)) (boot counter data choices rest) =
          (.ok (.nativeReference (counter + 6)), pinned counter data choices rest after) ∧
      after.visible = disk (logBytes values) ∧ after.durable = disk (logBytes values) := by
  obtain ⟨after, rfl, rfl, visible, durable, _⟩ :=
    arbitrary_repair_result counter data choices rest values maxRecords positive bounded image owner world trace
  let wrap : Reply → Result (Except Exception Reply) := fun reply => .ok (.ok reply)
  let handler : Exception → Result (Except Exception Reply) := fun error =>
    match error with
    | .error (.atom "rust_panicked") => .ok (.error (.error (.atom "nif_panicked")))
    | _ => .error .exhausted
  let finish : Except Exception Reply → Result Term := fun outcome =>
    match outcome with
    | .ok (.Ok owner) => do
      let term ← NativeResourceArc.encode owner
      NativeOwnedDrop.drop owner
      Result.ok term
    | .ok (.Err error) => Result.ofExcept error.convert
    | .error exception => .error exception
  have continued := (((trace.bind wrap).handle handler).bind finish).run []
  simp only [Result.ok_bind, wrap, Result.handle, finish] at continued
  refine ⟨after, ?_, visible, durable⟩
  unfold Rustler.withNativeResult
  dsimp only
  dsimp only [handler] at continued
  convert continued.trans (pin_resource counter data choices rest after positive) using 2
  congr 2
  funext outcome
  cases outcome with
  | error exception => rfl
  | ok reply => cases reply <;> rfl

end Record.NamedRustlerAdapterProof
