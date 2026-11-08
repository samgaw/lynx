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

private def incrementSharedCell : Result := .get fun env =>
  .set {env with refCounter := env.refCounter + 1, nativeHeap := [(1, "counter", .integer (env.refCounter + 1))]}
    (.wait (fun env => some ((), env)) (fun _ => .get fun env => .ok (.integer env.refCounter)))

private def counterShared (counter : Nat) : Nat × List (Nat × String × Term) :=
  (counter, [(1, "counter", .integer counter)])

private theorem incrementSharedTrace (pid counter : Nat) (heap : List (Nat × String × Term)) :
    Result.SharedSteps pid incrementSharedCell (counter, heap) (.integer (counter + 1))
      (counterShared (counter + 1)) := by
  unfold incrementSharedCell
  refine .update _
    (.wait (fun env => some ((), env)) (fun _ => .get fun env => .ok (.integer env.refCounter)))
    _ (counterShared (counter + 1)) _ _ ?_ ?_
  · intro env _ count _
    simp [counterShared, count]
  · refine .wait _ _ () _ (counterShared (counter + 1)) _ _ ?_ ?_
    · intro env _ count stored
      cases env
      simp_all [counterShared]
    · refine .read _ (.ok (.integer (counter + 1))) _ _ _ ?_ (.done _ _)
      intro env _ count _
      simp [counterShared] at count
      simp [count]

/-- The complete scheduled computations retain their get/set and wait nodes.
The root observes its increment, then the child advances the shared cell. -/
theorem scheduled_shared_read_write_wait :
    (Result.schedule incrementSharedCell (fun _ => incrementSharedCell)) {} =
      (.ok (.integer 1), {pidCounter := 2, refCounter := 2, nativeHeap := [(1, "counter", .integer 2)]}) := by
  simpa [counterShared] using Result.two_shared_serial_steps incrementSharedCell incrementSharedCell
    (.integer 1) (.integer 2) (0, []) (counterShared 1) (counterShared 2)
    (incrementSharedTrace 1 0 []) (incrementSharedTrace 2 1 (counterShared 1).2)

/-- The swap is consumed at the wait, after the parent's local read/write.
The child advances the shared counter before the parent observes it again. -/
theorem shared_wait_preserves_local_steps :
    (Result.schedule incrementSharedCell (fun _ => incrementSharedCell))
      {schedule := [.current, .swap 2]} =
      (.ok (.integer 2), {pidCounter := 2, refCounter := 2, nativeHeap := [(1, "counter", .integer 2)]}) := by
  cbv

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
