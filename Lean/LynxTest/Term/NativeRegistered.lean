module

import Lynx.Term.NativeTrace.Registered
meta import LynxTest.ProofAudit

namespace LynxTest.Term.NativeRegistered

open Lynx

private def acquire (env : Environment) : Option (Nat × Environment) :=
  let tag := if env.currentPid = [] then "parent" else "child"
  if env.nativeResourceTypes.contains tag && env.nativeHeap.isEmpty then
    some (env.nativeRefCounter, {env with nativeHeap := [(1, "owner", .pid env.currentPid)]})
  else none

private def release (value : Nat) (env : Environment) : Option (Unit × Environment) :=
  match env.nativeHeap with
  | [(1, "owner", .pid owner)] =>
      if owner == env.currentPid then
        some ((), {env with nativeRefCounter := value + 1, nativeHeap := []}) else none
  | _ => none

private def critical (value : Nat) : Result Term :=
  .wait (release value) fun _ => .ok (.integer (value + 1))

private def parent : Result Term :=
  .nativeModify (fun env => ((), {env with nativeResourceTypes := env.nativeResourceTypes ++ ["parent"]}))
    fun _ => .wait acquire critical

private def childRead (env : Environment) : Result Term :=
  if env.nativeResourceTypes.contains "parent" then
    .nativeSet {env with nativeResourceTypes := env.nativeResourceTypes ++ ["child"]} (.wait acquire critical)
  else .error (.error (.atom "badarg"))

private def childTransition (env : Environment) : Bool × Environment :=
  if env.nativeResourceTypes.contains "parent" then
    (true, {env with nativeResourceTypes := env.nativeResourceTypes ++ ["child"]})
  else (false, env)

private def childStart (registered : Bool) : Result Term :=
  if registered then .wait acquire critical else .error (.error (.atom "badarg"))

private theorem parent_prefix (counter : Nat) :
    Result.RegisteredPrefix [] parent (counter, []) [] (.wait acquire critical) (counter, []) ["parent"] := by
  refine .modify _ _ () _ (counter, []) _ _ ["parent"] _ _ ?_ (.refl _ _ _)
  intro env _ count heap registered
  simp [count, heap, registered]

private theorem child_read_prefix (counter : Nat) :
    Result.RegisteredPrefix [1] (.nativeGet childRead) (counter, [(1, "owner", .pid [])]) ["parent"]
      (.wait acquire critical) (counter, [(1, "owner", .pid [])]) ["parent", "child"] := by
  refine .update _ _ _ (counter, [(1, "owner", .pid [])]) _ _ ["parent", "child"] _ _ ?_ (.refl _ _ _)
  intro env _ count heap registered
  simp [childRead, count, heap, registered]

private theorem child_modify_prefix (counter : Nat) :
    Result.RegisteredPrefix [1] (.nativeModify childTransition childStart)
      (counter, [(1, "owner", .pid [])]) ["parent"] (.wait acquire critical)
      (counter, [(1, "owner", .pid [])]) ["parent", "child"] := by
  refine .modify _ _ true _ (counter, [(1, "owner", .pid [])]) _ _ ["parent", "child"] _ _ ?_ (.refl _ _ _)
  intro env _ count heap registered
  simp [childTransition, count, heap, registered]

private theorem critical_trace (pid : PID) (value : Nat) :
    Result.SharedSteps pid (critical value) (value, [(1, "owner", .pid pid)])
      (.integer (value + 1)) (value + 1, []) := by
  refine .wait _ _ () _ (value + 1, []) _ _ ?_ (.done _ _)
  intro env owner _ heap
  cases env
  simp_all [release]

/-- Actual read/set registration and both native updates retain both types.
The peer cannot acquire until the owner's release, and then needs its type. -/
theorem read_set_registration (counter : Nat) :
    (Result.schedule {} (.nativeGet childRead) (fun _ => parent)).run
      {nativeRefCounter := counter} [.current, .swap [1]] =
      (.ok (.integer (counter + 1)), {
        nativeRefCounter := counter + 2, nativeResourceTypes := ["parent", "child"]}) := by
  exact Result.two_registered_interleave_steps parent childRead acquire critical acquire critical
    counter (counter + 1) (.integer (counter + 1)) (.integer (counter + 2))
    (counter, []) (counter, []) (counter, [(1, "owner", .pid [])])
    (counter, [(1, "owner", .pid [])]) (counter + 1, [])
    (counter + 1, [(1, "owner", .pid [1])]) (counter + 2, [])
    [] ["parent"] ["parent", "child"] (parent_prefix counter) (child_read_prefix counter)
    (by simp [acquire]) (critical_trace [] counter) (by simp [acquire])
    (by simp [acquire]) (critical_trace [1] (counter + 1))

/-- The atomic registration prefix obeys the same actual contended schedule. -/
theorem atomic_registration (counter : Nat) :
    (Result.schedule {} (.nativeModify childTransition childStart) (fun _ => parent)).run
      {nativeRefCounter := counter} [.current, .swap [1]] =
      (.ok (.integer (counter + 1)), {
        nativeRefCounter := counter + 2, nativeResourceTypes := ["parent", "child"]}) := by
  exact Result.two_registered_modify_interleave_steps parent childTransition childStart acquire critical acquire critical
    counter (counter + 1) (.integer (counter + 1)) (.integer (counter + 2))
    (counter, []) (counter, []) (counter, [(1, "owner", .pid [])])
    (counter, [(1, "owner", .pid [])]) (counter + 1, [])
    (counter + 1, [(1, "owner", .pid [1])]) (counter + 2, [])
    [] ["parent"] ["parent", "child"] (parent_prefix counter) (child_modify_prefix counter)
    (by simp [acquire]) (critical_trace [] counter) (by simp [acquire])
    (by simp [acquire]) (critical_trace [1] (counter + 1))

/-- The callback guard is actual code, rather than an assumed registration. -/
theorem missing_parent_rejected :
    childRead {} = .error (.error (.atom "badarg")) ∧
    childTransition {} = (false, {}) ∧
    childStart false = .error (.error (.atom "badarg")) :=
  ⟨rfl, rfl, rfl⟩

end LynxTest.Term.NativeRegistered

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Term.NativeTrace.Registered
  LynxTest.ProofAudit.checkModule `LynxTest.Term.NativeRegistered
