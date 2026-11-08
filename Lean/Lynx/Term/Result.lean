module

public import Lynx.Term.DataTypes

/-! Combinators over resumable computations that translated impure code uses,
with the equations proofs and well-founded preprocessing need. Their `Except`
counterparts for pure code are in `Lynx.Term.Except`. -/

public section

namespace Lynx.Result

/-- Atomically consume one uniquely registered live native capability. Host
admission must establish what the tag certifies; this primitive does not validate
native memory, FFI or cleanup behavior. Invalid identities exhaust verification
without changing state. -/
@[expose] def consumeNativeCapability (typeName : String) (identity : Nat) : Result Unit :=
  .wait (fun env => some (
    if identity = 0 ∨ env.nativeRefCounter < identity then
      ((Except.error .exhausted : Except Exception Unit), env)
    else match env.nativeHeap.filter (fun cell => cell.1 == identity) with
    | [(_,storedType,.atom "live")] =>
      if storedType == typeName then
        (Except.ok (), {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != identity)})
      else (Except.error .exhausted, env)
    | _ => (Except.error .exhausted, env))) Result.ofExcept

/-- Erlang guards select their body only on the atom `true`. -/
@[expose] def guardPassed : Result → Bool
  | .ok (.atom value) => value == "true"
  | _ => false

/-- Run a Core guard, falling through on exceptions and values other than `true`. -/
@[expose] def guard (computation : Result) (body next : Unit → Result α) : Result α :=
  computation.tryWith
    (fun value => match value with | .atom "true" => body () | _ => next ())
    (fun _ => next ())

@[simp] theorem guard_eq (computation : Result) (body next : Unit → Result α) :
    computation.guard body next = computation.tryWith
      (fun value => match value with | .atom "true" => body () | _ => next ())
      (fun _ => next ()) := rfl

@[simp↓] theorem IsPure.guard (computation : Result) (body next : Unit → Result α)
    (pure : computation.IsPure) (bodyPure : ∀ token, (body token).IsPure)
    (nextPure : ∀ token, (next token).IsPure) :
    (computation.guard body next).IsPure := by
  unfold Result.guard
  apply IsPure.tryWith _ _ _ pure
  · intro value
    split <;> simp_all
  · exact fun _ => nextPure ()

/-- Whether a computation did not return. -/
@[expose] def isExhausted : Result α → Bool
  | .error .exhausted => true
  | _ => false

-- Termination proofs see which branch a guard selected.
@[wf_preprocess] theorem guard_wf (computation : Result) (pure : computation.IsPure)
    (body next : Unit → Result α) :
    computation.guard body next =
      (if computation.isExhausted then .error .exhausted
        else if computation.guardPassed then body () else next ()) := by
  cases computation with
  | ok value =>
    simp only [guard_eq, tryWith_ok]
    cases value <;> simp [guardPassed, isExhausted]
    rename_i value
    by_cases accepted : value = "true" <;> simp_all
  | error exception => cases exception <;> rfl
  | _ => exact False.elim pure

end Lynx.Result
