module
public import Runtime.Critical.Funs
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.CriticalConcurrent

-- Intended bounded concurrency property. The current public runner interface
-- cannot reduce the scheduled execution; this fixture deliberately fails.
/-- Two actual extracted critical sections preserve both writes under this
contending schedule. Native contexts here are modeled local Lynx processes. -/
theorem updates_interleave :
    let worker := fun amount : U64 => (do
      let changed ← locked_increment ⟨1⟩ amount
      return if changed then Term.true else Term.false : Result Term)
    let computation : Result Term := do
      let _ ← Result.schedule (worker 3#u64) .ok
      worker 4#u64
    let observed := computation {
      refCounter := 1
      nativeHeap := [(1, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk 7#u64)])]
      schedule := [.current, .swap 2]
    }
    observed.1 = .ok Term.true ∧ observed.2.nativeHeap =
      [(1, NativeMutex.typeName effects_core.Counter,
        .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (effects_core.Counter.mk 14#u64)])] := by
  cbv

end Runtime.CriticalConcurrent
