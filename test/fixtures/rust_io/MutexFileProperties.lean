module
public import MutexFile.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace MutexFile.Properties

@[expose] def live (file : NativeFile) (state : NativeFile.State) (poisoned : Bool) : Environment :=
  {nativeRefCounter := file.id + 1, nativeHeap := [
    (file.id + 1, NativeMutex.typeName NativeFile,
      .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
        NativeCodec.encode file]),
    (file.id, NativeFile.typeName, NativeFile.encode state)]}

@[expose] def closed (file : NativeFile) (state : NativeFile.State) : Environment :=
  {nativeRefCounter := file.id + 1, nativeHeap := [
    (file.id, NativeFile.closedTypeName, NativeFile.encode state)]}

theorem consuming (file : NativeFile) (before after : NativeFile.State)
    (poisoned : Bool)
    (visible : before.visible.size ≤ NativeFile.limit)
    (durable : before.durable.size ≤ NativeFile.limit)
    (position : before.position ≤ NativeFile.limit)
    (ready : NativeFile.blocked before = false)
    (step : NativeFile.closeStep before = some after) :
    consume_file_mutex ⟨file.id + 1⟩ (live file before poisoned) =
      (.ok (), closed file after) := by
  have distinct : file.id ≠ file.id + 1 := by omega
  have nonnegative : ((before.position : Int) < 0) = False := by
    apply propext
    exact iff_false_intro (not_lt.mpr (Int.natCast_nonneg _))
  have poll : NativeFile.pollClose file (live file before poisoned) =
      some (.ok (), { (live file before poisoned) with nativeHeap := [
        (file.id + 1, NativeMutex.typeName NativeFile,
          .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"),
            NativeCodec.encode file]),
        (file.id, NativeFile.closedTypeName, NativeFile.encode after)] }) := by
    simp [NativeFile.pollClose, NativeFile.lookup, live, distinct, Ne.symm distinct,
      NativeFile.decode, NativeFile.encode, not_lt.mpr visible, not_lt.mpr durable,
      not_lt.mpr position, nonnegative, ready, step, NativeFile.retire]
  cases poisoned <;>
    simp [consume_file_mutex, io_core.consume_file_mutex, NativeOwnedDrop.drop, NativeMutex.disposeFile,
      NativeM.readCell, live, distinct, Ne.symm distinct, NativeCodec.decode,
      NativeCodec.encode, NativeMutex.typeName, NativeFile.close, Result.wait_bind]
  all_goals
    have expanded := poll
    simp [live, NativeMutex.typeName, NativeCodec.encode] at expanded
    have eta : (⟨file.id⟩ : NativeFile) = file := by cases file; rfl
    simp only [eta]
    rw [Result.wait_ready_apply _ _ _ _ _ expanded]
    simp [Result.ok_bind, NativeM.removeCell, live, closed, distinct, Ne.symm distinct,
      NativeMutex.typeName, NativeFile.closedTypeName]

theorem implicit_consuming (mutex : NativeMutex NativeFile) :
    implicit_file_mutex mutex = consume_file_mutex mutex := by rfl

@[expose] def initial (file : NativeFile) (state : NativeFile.State) : Environment :=
  {nativeRefCounter := file.id, nativeHeap := [(file.id, NativeFile.typeName, NativeFile.encode state)]}

theorem cycle (file : NativeFile) (before after : NativeFile.State)
    (visible : before.visible.size ≤ NativeFile.limit)
    (durable : before.durable.size ≤ NativeFile.limit)
    (position : before.position ≤ NativeFile.limit)
    (ready : NativeFile.blocked before = false)
    (step : NativeFile.closeStep before = some after) :
    file_mutex_cycle file (initial file before) = (.ok (), closed file after) := by
  have fresh : file.id ≠ file.id + 1 := by omega
  simp only [file_mutex_cycle, monadLift_self]
  simp [NativeMutex.new, NativeM.allocate, initial, fresh]
  exact consuming file before after false visible durable position ready step

@[expose] def closeChoice (success : Bool) : Term :=
  .cons (.tuple #[.atom "close", .atom (if success then "ok" else "error"),
    .integer 0, .bitstring ⟨#[0]⟩ 0]) .nil

/-- Mutex cleanup cannot turn an unsynchronized write into a durability promise. -/
theorem no_implicit_sync :
    file_mutex_cycle ⟨1⟩ (initial ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, closeChoice true⟩) =
      (.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩) := by
  apply cycle <;> first | rfl | decide

/-- Poisoning and an ignored close error both retain the consuming drop behavior. -/
theorem poisoned_close_error :
    consume_file_mutex ⟨2⟩ (live ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, closeChoice false⟩ true) =
      (.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩) := by
  apply consuming <;> first | rfl | decide

/-- Cleanup retains the file image for crash reasoning after retiring both owners. -/
theorem crash_after_cleanup :
    file_mutex_cycle ⟨1⟩ (initial ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, closeChoice true⟩) =
      (.ok (), closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩) ∧
    NativeFile.crashImage ⟨1⟩ ⟨#[0]⟩ (closed ⟨1⟩ ⟨⟨#[2]⟩, ⟨#[1]⟩, 0, .nil⟩) =
      some ⟨⟨#[1]⟩, 2⟩ := by
  exact ⟨no_implicit_sync, rfl⟩

/-- A malformed locked owner cannot silently discard the file or mutex cell. -/
theorem locked_rejected (state : NativeFile.State) :
    let env : Environment := {nativeRefCounter := 2, nativeHeap := [
      (2, NativeMutex.typeName NativeFile,
        .tuple #[.atom "locked", .atom "unpoisoned", .nativeReference 1]),
      (1, NativeFile.typeName, NativeFile.encode state)]}
    consume_file_mutex ⟨2⟩ env = (.error .exhausted, env) := by
  have different : (Term.atom "locked").compare (.atom "unlocked") ≠ .eq := by
    rw [Term.compare_atoms]
    intro equal
    have names := Std.LawfulEqCmp.eq_of_compare equal
    contradiction
  simp [consume_file_mutex, io_core.consume_file_mutex, NativeOwnedDrop.drop,
    NativeMutex.disposeFile, NativeM.readCell, different]

/-- A missing file choice fails verification without claiming that cleanup ran. -/
theorem missing_close_choice :
    consume_file_mutex ⟨2⟩ (live ⟨1⟩ ⟨⟨#[]⟩, ⟨#[]⟩, 0, .nil⟩ false) =
      (.error .exhausted, live ⟨1⟩ ⟨⟨#[]⟩, ⟨#[]⟩, 0, .nil⟩ false) := by
  have poll : NativeFile.pollClose ⟨1⟩
      (live ⟨1⟩ ⟨⟨#[]⟩, ⟨#[]⟩, 0, .nil⟩ false) =
      some (.error .exhausted, live ⟨1⟩ ⟨⟨#[]⟩, ⟨#[]⟩, 0, .nil⟩ false) := by
    simp [NativeFile.pollClose, NativeFile.lookup, live, NativeFile.decode, NativeFile.encode,
      NativeFile.blocked, NativeFile.closeStep, NativeFile.action, NativeFile.limit, ByteArray.size]
  simp [consume_file_mutex, io_core.consume_file_mutex, NativeOwnedDrop.drop,
    NativeMutex.disposeFile, NativeM.readCell, live, NativeMutex.typeName,
    NativeCodec.decode, NativeCodec.encode, NativeFile.close, Result.wait_bind]
  have expanded := poll
  simp [live, NativeMutex.typeName, NativeCodec.encode] at expanded
  rw [Result.wait_ready_apply _ _ _ _ _ expanded]
  simp

end MutexFile.Properties
