module
public import LockedBytes.NativeRuntime
open Aeneas Aeneas.Std Lynx
namespace LockedBytes.ModelTests
private abbrev Bytes := alloc.vec.Vec U8

private def live (value : Bytes) (flag : String) (env : Environment) : Environment :=
  {env with nativeHeap := [(1, NativeMutex.typeName Bytes,
    .tuple #[.atom "unlocked", .atom flag, NativeCodec.encode value])]}

theorem missing (env : Environment) (empty : env.nativeHeap = []) (schedule : List ScheduleChoice) :
    (NativeMutex.into_inner (α := Bytes) ⟨1⟩).run env schedule = (.error .exhausted, env) := by
  simp [NativeMutex.into_inner, NativeMutex.intoInnerStep, empty, Result.wait_run]

theorem unknown_poison (value : Bytes) (env : Environment) (schedule : List ScheduleChoice) :
    (NativeMutex.into_inner (α := Bytes) ⟨1⟩).run (live value "unknown" env) schedule =
      (.error .exhausted, live value "unknown" env) := by
  simp [NativeMutex.into_inner, NativeMutex.intoInnerStep, live, NativeCodec.roundtrip, Result.wait_run]

theorem malformed_value (env : Environment) (schedule : List ScheduleChoice) :
    let broken := {env with nativeHeap := [(1, NativeMutex.typeName Bytes,
      .tuple #[.atom "unlocked", .atom "unpoisoned", .atom "corrupt"])]}
    (NativeMutex.into_inner (α := Bytes) ⟨1⟩).run broken schedule = (.error .exhausted, broken) := by
  simp [NativeMutex.into_inner, NativeMutex.intoInnerStep, NativeCodec.decode,
    NativeCodec.decodeElements, Result.wait_run]

theorem wrong_type (env : Environment) (schedule : List ScheduleChoice) :
    let wrong := {env with nativeHeap := [(1, "wrong", .tuple #[.atom "unlocked", .atom "unpoisoned", .nil])]}
    (NativeMutex.into_inner (α := Bytes) ⟨1⟩).run wrong schedule = (.error .exhausted, wrong) := by
  simp [NativeMutex.into_inner, NativeMutex.intoInnerStep, NativeMutex.typeName,
    NativeCodec.typeName, Result.wait_run]

theorem duplicate (value : Bytes) (env : Environment) (schedule : List ScheduleChoice) :
    let cells := (live value "unpoisoned" env).nativeHeap
    let ambiguous := {env with nativeHeap := cells ++ cells}
    (NativeMutex.into_inner (α := Bytes) ⟨1⟩).run ambiguous schedule = (.error .exhausted, ambiguous) := by
  simp [NativeMutex.into_inner, NativeMutex.intoInnerStep, live, Result.wait_run]

theorem held (value : Bytes) (poisoned : Bool) (env : Environment) (schedule : List ScheduleChoice) :
    let locked := {env with nativeHeap := [(1, NativeMutex.typeName Bytes,
      NativeMutex.lockedContents env.currentPid 2 poisoned value)]}
    (NativeMutex.into_inner (α := Bytes) ⟨1⟩).run locked schedule = (.error .exhausted, locked) := by
  simp [NativeMutex.into_inner, NativeMutex.intoInnerStep, NativeMutex.lockedContents, Result.wait_run]

end LockedBytes.ModelTests
