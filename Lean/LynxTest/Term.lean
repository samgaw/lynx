import LynxTest.ProofAudit
import Lynx.Term

namespace LynxTest.Term

open Lynx

example : Result = Result Lynx.Term := rfl

-- Bind can change the success type, while ordinary results default to Term.
theorem generic_result_bind :
    ((pure 7 : Result Nat) >>= fun n => (pure (.integer n) : Result)) =
      .ok (.integer 7) := rfl

theorem generic_result_catch (exception : Exception) (handler : Exception → Result Nat)
    (raised : exception ≠ .exhausted) :
    tryCatch (throw exception : Result Nat) handler = handler exception := by
  cases exception <;> first | rfl | contradiction

-- Constant computations distinguish success and the three Erlang exception classes.
theorem result_constructors :
    (Result.ok .nil : Result) = .ok .nil ∧
    (Result.ok .nil : Result) ≠ .error (.error .nil) ∧
    (Result.error (.error .nil) : Result) ≠ .ok .nil ∧
    (Result.error (.throw .nil) : Result) = .error (.throw .nil) ∧
    (Result.error (.error .nil) : Result) ≠ .error (.throw .nil) ∧
    (Result.error (.throw .nil) : Result) ≠ .error (.exit .nil) ∧
    (Result.error (.error (.tuple #[.atom "badkey", .nil])) : Result) ≠
      .error (.error (.tuple #[.atom "badmap", .nil])) := by simp

/-- Updating the process dictionary never discards shared native cells. -/
theorem nativeHeap_pdict (env : Environment) (dictionary : List (Term × Term)) :
    (env.setPdict dictionary).nativeHeap = env.nativeHeap := rfl

private def publishNativeCell : Result := .get fun env =>
  .set { env with nativeHeap := [(1, "counter", .integer 7)] }
    (.get fun env => .set (env.setPdict [(.atom "worker", .atom "only")]) (.ok .nil))

private def nativeCellExchange : Result :=
  .schedule publishNativeCell fun _ => .get fun env => .ok (.integer env.nativeHeap.length)

/-- The child and parent share native storage, while process dictionaries remain local.
These concrete schedules exercise scheduler save/activate and process completion. -/
theorem nativeHeap_shared_processes :
    (nativeCellExchange.run { schedule := [.swap 2] }) =
      (.ok (.integer 1), { pidCounter := 2, nativeHeap := [(1, "counter", .integer 7)] }) ∧
    (nativeCellExchange.run { schedule := [.current] }) =
      (.ok (.integer 0), { pidCounter := 2, nativeHeap := [(1, "counter", .integer 7)] }) := by
  cbv
  constructor <;> rfl

/-- A failure preserves the shared heap accumulated before the exception. -/
theorem nativeHeap_before_failure (env : Environment) :
    (Result.set { env with nativeHeap := [(1, "counter", .integer 7)] }
      (.error (.throw (.atom "failed"))) : Result) env =
      (.error (.throw (.atom "failed")),
        { env with nativeHeap := [(1, "counter", .integer 7)] }) := by
  rfl

end LynxTest.Term

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term
  LynxTest.ProofAudit.checkModule `LynxTest.Term
  LynxTest.ProofAudit.checkModule `Lynx.Term.DataTypes
  LynxTest.ProofAudit.checkModule `Lynx.Term.FiniteFloat
  LynxTest.ProofAudit.checkModule `Lynx.Term.Bitstring
  LynxTest.ProofAudit.checkModule `Lynx.Term.Induction
  -- This structural proof needs only these standard kernel axioms.
  LynxTest.ProofAudit.checkDeclaration ``Lynx.Term.induct #[``propext, ``Quot.sound]
