module
public import Phase.Extraction.Funs
public import Phase.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Phase.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem start_contract (budget : U64) :
    atomic_core.start_phase budget = NativeM.ok
      (if budget = 0#u64 then .Ready else .Receiving budget 0#u64) := by
  unfold atomic_core.start_phase
  split <;> simp [NativeM.lift, NativeM.ok]

theorem terminal_stable (phase : atomic_core.Phase) (amount : U64)
    (terminal : ∀ limit used, phase ≠ .Receiving limit used) :
    atomic_core.consume_phase phase amount = NativeM.ok (false, phase) := by
  cases phase with
  | Ready => rfl
  | Complete total => rfl
  | Rejected code => rfl
  | Receiving limit used => exact (terminal limit used rfl).elim

theorem completion_total (completion : atomic_core.Completion) :
    atomic_core.phase_total (.Complete completion) = NativeM.ok completion.total := rfl

theorem receiving_bounded (limit used amount : U64) :
    ∃ accepted updated,
      atomic_core.consume_phase (.Receiving limit used) amount = NativeM.ok (accepted, updated) ∧
      (if accepted then ∃ total,
        atomic_core.phase_total updated = NativeM.ok total ∧
        total.val = used.val + amount.val ∧ total.val ≤ limit.val
       else updated = .Rejected 1#u8 ∧ limit.val < used.val + amount.val) := by
  have arithmetic := U64.checked_add_bv_spec used amount
  cases checked : U64.checked_add used amount with
  | none =>
    simp only [checked] at arithmetic
    refine ⟨false, .Rejected 1#u8, ?_, ?_⟩
    · simp [atomic_core.consume_phase, checked, NativeM.lift, NativeM.ok]
    · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
      scalar_tac
  | some total =>
    simp only [checked] at arithmetic
    by_cases less : total.val < limit.val
    · refine ⟨true, .Receiving limit total, ?_, ?_⟩
      · simp [atomic_core.consume_phase, checked, less, NativeM.lift, NativeM.ok]
      · refine ⟨total, ?_, arithmetic.2.1, ?_⟩
        · simp [atomic_core.phase_total, NativeM.ok]
        · scalar_tac
    · by_cases equal : total = limit
      · refine ⟨true, .Complete ⟨total, .Exact⟩, ?_, ?_⟩
        · simp [atomic_core.consume_phase, checked, less, equal, NativeM.lift, NativeM.ok]
        · exact ⟨total, rfl, arithmetic.2.1, by scalar_tac⟩
      · refine ⟨false, .Rejected 1#u8, ?_, ?_⟩
        · simp [atomic_core.consume_phase, checked, less, equal, NativeM.lift, NativeM.ok]
        · simp only [Bool.false_eq_true, ↓reduceIte, true_and]
          scalar_tac

theorem locked_contract (mutex : NativeMutex atomic_core.Phase) (amount : U64) :
    atomic_analysis.consume_locked mutex amount = (do
      let acquired ← NativeMutex.lock mutex
      let guard := match acquired with
        | .Ok guard => guard
        | .Err error => NativePoisonError.into_inner error
      let (accepted, updated) ← atomic_core.consume_phase guard.value amount
      let total ← atomic_core.phase_total updated
      NativeGuard.release {guard with value := updated}
      .ok (accepted, total)) := by
  simp [atomic_analysis.consume_locked, NativeGuard.deref_mut, NativeGuard.deref,
    NativeOwnedDrop.drop, NativeM.lift, NativeM.ok]
  congr 1
  funext acquired
  cases acquired <;> simp [NativePoisonError.into_inner]

theorem facade_contract (budget first second : U64) :
    __NIF__ budget first second = (do
      let initial ← atomic_core.start_phase budget
      let phase ← NativeMutex.new initial
      let (acceptedFirst, _) ← atomic_analysis.consume_locked phase first
      let (acceptedSecond, total) ← atomic_analysis.consume_locked phase second
      NativeOwnedDrop.drop phase
      .ok (acceptedFirst, acceptedSecond, total)) := rfl

theorem facade_run (budget first second : U64)
    (initial middle finalPhase : atomic_core.Phase) (acceptedFirst acceptedSecond : Bool)
    (firstTotal finalTotal : U64)
    (started : atomic_core.start_phase budget = NativeM.ok initial)
    (firstStep : atomic_core.consume_phase initial first = NativeM.ok (acceptedFirst, middle))
    (firstRead : atomic_core.phase_total middle = NativeM.ok firstTotal)
    (secondStep : atomic_core.consume_phase middle second = NativeM.ok (acceptedSecond, finalPhase))
    (secondRead : atomic_core.phase_total finalPhase = NativeM.ok finalTotal)
    (env : Environment) (empty : env.nativeHeap = []) (schedule : List ScheduleChoice) :
    (__NIF__ budget first second).run env schedule =
      (.ok (acceptedFirst, acceptedSecond, finalTotal),
        {env with nativeRefCounter := env.nativeRefCounter + 3}) := by
  simp [facade_contract, locked_contract, started,
    NativeMutex.new, NativeM.allocate, empty, NativeMutex.lock, NativeMutex.pollLock,
    NativeCodec.roundtrip, firstStep, firstRead, secondStep, secondRead,
    NativeOwnedDrop.drop, NativeGuard.release, NativeGuard.pollRelease,
    NativeMutex.dispose, NativeM.readCell, NativeM.removeCell,
    NativeM.ok, Result.wait_run, Result.wait_bind, Nat.add_assoc]

theorem invalid_nested_kind :
    NativeCodec.decode (α := atomic_core.Completion)
      (.cons (.atom (NativeCodec.typeName (α := atomic_core.Completion)))
        (Term.list [.integer 1, .atom "Exact"])) = none := by cbv

/-- Invalid logical variants never become a Rust value. -/
theorem invalid_variant :
    NativeCodec.decode (α := atomic_core.Phase)
      (.cons (.atom (NativeCodec.typeName (α := atomic_core.Phase)))
        (.cons (.atom "Unknown") .nil)) = none := by cbv

theorem invalid_arity :
    NativeCodec.decode (α := atomic_core.Phase)
      (.cons (.atom (NativeCodec.typeName (α := atomic_core.Phase)))
        (.cons (.atom "Receiving") (.cons (.integer 1) .nil))) = none := by cbv

theorem invalid_code_range :
    NativeCodec.decode (α := atomic_core.Phase)
      (.cons (.atom (NativeCodec.typeName (α := atomic_core.Phase)))
        (.cons (.atom "Rejected") (.cons (.integer 256) .nil))) = none := by cbv

end Phase.Properties
