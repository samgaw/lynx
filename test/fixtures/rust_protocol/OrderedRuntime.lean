module
public import __PREFIX__.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx
open __PREFIX__.Extraction.OrderedCollections

namespace __PREFIX__.Properties

theorem replace_eq (table : Map) (key value : U64)
    (bounded : table.size ≤ 262144)
    (space : table.size < 262144 ∨ table.contains key.val = true) :
    __CORE__.replace_value table key value =
      NativeM.ok (table[key.val]?, table.insert key.val value) := by
  unfold __CORE__.replace_value mapInsert
  rw [if_pos ⟨bounded, space⟩]
  rfl

theorem locked_contract (table : NativeMutex Map) (key value : U64) :
    __CORE__.locked_replace table key value = (do
      let acquired ← NativeMutex.lock table
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let (previous, updated) ← __CORE__.replace_value guard.value key value
      NativeGuard.release {guard with value := updated}
      .ok previous) := by
  simp [__CORE__.locked_replace, NativeGuard.deref_mut, NativeDrop.drop, NativeOwnedDrop.drop,
    NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

@[expose] def state (table : Map) (poisoned : Bool) (env : Environment) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(1, NativeMutex.typeName Map,
    .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode table])]}

theorem replace_run (table : Map) (key value : U64) (poisoned : Bool)
    (bounded : table.size ≤ 262144)
    (space : table.size < 262144 ∨ table.contains key.val = true)
    (env : Environment) (schedule : List ScheduleChoice) :
    (__ANALYSIS__.registry_replace ⟨1⟩ key value).run (state table poisoned env) schedule =
      (.ok table[key.val]?, {state (table.insert key.val value) poisoned env with nativeRefCounter := 2}) := by
  have replaced := replace_eq table key value bounded space
  cases poisoned <;>
    simp [__ANALYSIS__.registry_replace, locked_contract, state, NativeMutex.lock,
      NativeMutex.pollLock, NativeCodec.roundtrip, replaced, NativeGuard.release,
      NativeGuard.pollRelease, NativeM.ok, Result.wait_run, Result.wait_bind]
theorem replace_preserves_other (table : Map) (key value : U64) (other : Nat)
    (bounded : table.size ≤ 262144)
    (space : table.size < 262144 ∨ table.contains key.val = true)
    (different : other ≠ key.val) :
    ∃ previous updated, __CORE__.replace_value table key value = NativeM.ok (previous, updated) ∧
      updated[other]? = table[other]? := by
  refine ⟨table[key.val]?, table.insert key.val value, replace_eq table key value bounded space, ?_⟩
  simp [Std.ExtTreeMap.getElem?_insert, different, Ne.symm different]

theorem take_eq (table : Map) (key : U64) (bounded : table.size ≤ 262144) :
    __CORE__.take table key = NativeM.ok (table[key.val]?, table.erase key.val) := by
  unfold __CORE__.take mapRemove
  rw [if_pos bounded]
  rfl

theorem take_contract (table : NativeMutex Map) (key : U64) :
    __CORE__.locked_take table key = (do
      let acquired ← NativeMutex.lock table
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let (previous, updated) ← __CORE__.take guard.value key
      NativeGuard.release {guard with value := updated}
      .ok previous) := by
  simp [__CORE__.locked_take, NativeGuard.deref_mut, NativeDrop.drop, NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

theorem take_run (table : Map) (key : U64) (poisoned : Bool)
    (bounded : table.size ≤ 262144) (env : Environment) (schedule : List ScheduleChoice) :
    (__ANALYSIS__.registry_take ⟨1⟩ key).run (state table poisoned env) schedule =
      (.ok table[key.val]?, {state (table.erase key.val) poisoned env with nativeRefCounter := 2}) := by
  have taken := take_eq table key bounded
  cases poisoned <;>
    simp [__ANALYSIS__.registry_take, take_contract, state, NativeMutex.lock,
      NativeMutex.pollLock, NativeCodec.roundtrip, taken, NativeGuard.release,
      NativeGuard.pollRelease, NativeM.ok, Result.wait_run, Result.wait_bind]

theorem claim_eq (values : Set) (key : U64) (bounded : values.size ≤ 262144)
    (space : values.size < 262144 ∨ values.contains key.val = true) :
    __CORE__.claim values key = NativeM.ok (!values.contains key.val, values.insert key.val) := by
  unfold __CORE__.claim setInsert
  rw [if_pos ⟨bounded, space⟩]
  rfl

theorem claim_contract (values : NativeMutex Set) (key : U64) :
    __CORE__.locked_claim values key = (do
      let acquired ← NativeMutex.lock values
      let guard := match acquired with | .Ok guard => guard | .Err error => error.value
      let (claimed, updated) ← __CORE__.claim guard.value key
      NativeGuard.release {guard with value := updated}
      .ok claimed) := by
  simp [__CORE__.locked_claim, NativeGuard.deref_mut, NativeDrop.drop, NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

@[expose] def setState (values : Set) (poisoned : Bool) (env : Environment) : Environment :=
  {env with nativeRefCounter := 1, nativeHeap := [(1, NativeMutex.typeName Set,
    .tuple #[.atom "unlocked", .atom (if poisoned then "poisoned" else "unpoisoned"), NativeCodec.encode values])]}

theorem claim_run (values : Set) (key : U64) (poisoned : Bool)
    (bounded : values.size ≤ 262144)
    (space : values.size < 262144 ∨ values.contains key.val = true)
    (env : Environment) (schedule : List ScheduleChoice) :
    (__ANALYSIS__.registry_claim ⟨1⟩ key).run (setState values poisoned env) schedule =
      (.ok (!values.contains key.val), {setState (values.insert key.val) poisoned env with nativeRefCounter := 2}) := by
  have claimed := claim_eq values key bounded space
  cases poisoned <;>
    simp [__ANALYSIS__.registry_claim, claim_contract, setState, NativeMutex.lock,
      NativeMutex.pollLock, NativeCodec.roundtrip, claimed, NativeGuard.release,
      NativeGuard.pollRelease, NativeM.ok, Result.wait_run, Result.wait_bind]
end __PREFIX__.Properties
