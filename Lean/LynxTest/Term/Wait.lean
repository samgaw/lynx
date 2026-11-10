module

import Lynx
-- This module audits the private scheduler and its structural progress proof.
import all Lynx.Term.Runner
meta import LynxTest.ProofAudit

namespace LynxTest.Term.Wait
open Lynx

/-- Waiting does not manufacture progress when the closed process tree is blocked. -/
theorem blocked_has_no_success :
    ((Result.wait (α := Term) (β := Unit) (fun _ => none) (fun _ => .ok (.atom "finished"))) {}).1 = .deadlock := by
  cbv

/-- A blocked native operation preserves its configured finalizer policy and
shared heap instead of falling back to a fresh ordinary process environment. -/
theorem blocked_preserves_native_environment (mode : NativeFinalizerMode)
    (choices : List ScheduleChoice) :
    let env : Environment := {
      currentPid := [3], nativeFinalizerMode := mode
      nativeRefCounter := 7, nativeHeap := [(4, "resource", .atom "retained")]
      nativeResourceTypes := ["registered"]}
    (Result.wait (β := Unit) (fun _ => none) (fun _ => Result.ok Term.true)).run env choices =
      (.deadlock, env) := by
  exact Result.wait_blocked_run _ _ _ rfl choices

/-- Committing a native poll preserves every process mailbox. A blocked poll
has no commit at all, and a ready poll cannot overwrite VM messages. -/
theorem blocked_preserves_mailbox (state : Concurrent.State) (pid target : PID) (env : Environment) :
    ((state.storeNative pid env).process target).mailbox = (state.process target).mailbox := by
  by_cases same : target = pid
  · subst target
    simp [Concurrent.State.storeNative, Concurrent.State.store, Concurrent.State.process,
      Concurrent.State.update]
  · simp [Concurrent.State.storeNative, Concurrent.State.store, Concurrent.State.process,
      Concurrent.State.update, same]

private def published : Result Term :=
  .nativeGet fun env => .nativeSet { env with nativeHeap := [(1, "cell", .integer 7)] } (.ok .nil)

private def awaitValue : Result Term :=
  .wait (fun env => match env.nativeHeap with
    | [(_, _, value)] => some (value, env)
    | _ => none) .ok

/-- A blocked waiter resumes after another process changes shared state. -/
theorem state_change_wakes_waiter :
    (do let _ ← Result.schedule {} published .ok; awaitValue)
      {} =
      (.ok (.integer 7), {

        nativeHeap := [(1, "cell", .integer 7)]
      }) := by cbv

private def claim (env : Environment) : Option (Unit × Environment) :=
  if env.nativeRefCounter == 0 then some ((), { env with nativeRefCounter := 1 }) else none

private def compete : Result Term := do
  let _ ← Result.schedule {} (.wait claim fun _ => .ok .nil) .ok
  .wait claim fun _ => .ok .nil

/-- Readiness and the update are atomic: two ready requests cannot both claim. -/
theorem exactly_one_claim :
    (compete.run {} [.current]).1 = .deadlock ∧
    (compete.run {} [.current]).2.nativeRefCounter = 1 ∧
    (compete.run {} [.swap [1]]).1 = .deadlock ∧
    (compete.run {} [.swap [1]]).2.nativeRefCounter = 1 := by cbv

-- These synthetic polls isolate scheduler behavior. Rust implementation
-- correspondence is checked separately against actual extracted functions.
private def acquire (env : Environment) : Option (Nat × Environment) :=
  if env.nativeHeap.isEmpty then
    some (env.nativeRefCounter, { env with nativeHeap := [(1, "owner", .pid env.currentPid)] })
  else none

private def release (value : Nat) (env : Environment) : Option (Unit × Environment) :=
  match env.nativeHeap with
  | [(1, "owner", .pid owner)] =>
    if owner == env.currentPid then
      some ((), { env with nativeHeap := [], nativeRefCounter := value }) else none
  | _ => none

private def update : Result Term := do
  let value ← Result.wait acquire .ok
  Result.wait (release (value + 1)) fun _ => .ok .nil

private def updates : Result Term := do
  let _ ← Result.schedule {} update .ok
  update

/-- Releasing wakes a contending process without losing its protected update. -/
theorem contending_updates_complete :
    updates.run {} [.current, .swap [1]] = (.ok .nil, {  nativeRefCounter := 2 }) ∧
    updates.run {} [.swap [1], .swap []] = (.ok .nil, {  nativeRefCounter := 2 }) := by cbv

private def tick (env : Environment) : Option (Unit × Environment) :=
  some ((), {env with nativeRefCounter := env.nativeRefCounter + 1})

private def postUpdate (value : Nat) : Result Term :=
  .wait tick fun _ => .wait tick fun _ => .wait (release (value + 3)) fun _ => .ok .nil

private theorem update_exclusive (pid peer : PID) (value : Nat) :
    Result.ExclusiveSteps pid peer acquire (postUpdate value)
      (value, [(1, "owner", .pid pid)]) .nil (value + 3, []) := by
  refine .wait _ _ () _ (value + 1, [(1, "owner", .pid pid)]) _ _ ?_ ?_ ?_
  · intro env owner counter heap
    simp [tick, counter, heap]
  · intro env owner counter heap
    simp [acquire, heap]
  · refine .wait _ _ () _ (value + 2, [(1, "owner", .pid pid)]) _ _ ?_ ?_ ?_
    · intro env owner counter heap
      simp [tick, counter, heap, Nat.add_assoc]
    · intro env owner counter heap
      simp [acquire, heap]
    · refine .wait _ _ () _ (value + 3, []) _ _ ?_ ?_ ?_
      · intro env owner counter heap
        simp [release, heap, owner]
      · intro env owner counter heap
        simp [acquire, heap]
      · exact .done Term.nil _

private theorem update_trace (pid : PID) (value : Nat) :
    Result.SharedSteps pid (postUpdate value) (value, [(1, "owner", .pid pid)]) .nil (value + 3, []) :=
  (update_exclusive pid (pid ++ [1]) value).ready

private theorem update_full (pid : PID) (value : Nat) :
    Result.SharedSteps pid (.wait acquire postUpdate) (value, []) .nil (value + 3, []) := by
  refine .wait _ _ value _ (value, [(1, "owner", .pid pid)]) _ _ ?_ (update_trace pid value)
  intro env owner counter heap
  simp [acquire, heap, counter, owner]

/-- Finite ready traces retain process-local fields alongside shared updates. -/
theorem ready_trace_frames_environment (env : Environment) (value : Nat)
    (empty : env.nativeHeap = []) (count : env.nativeRefCounter = value) :
    (Result.wait acquire postUpdate) env =
      (.ok .nil, {env with nativeRefCounter := value + 3, nativeHeap := []}) :=
  (update_full env.currentPid value).apply env rfl count empty

/-- Intermediate ready waits remain scheduler steps while a competitor blocks;
the same shared cells survive through both complete worker traces. -/
theorem contending_multi_wait_updates :
    (Result.schedule {} (.wait acquire postUpdate) (fun _ => .wait acquire postUpdate)).run
      {} [.current, .swap [1]] =
      (.ok .nil, { nativeRefCounter := 6}) := by
  exact Result.two_wait_interleave_steps acquire postUpdate acquire postUpdate 0 3 .nil .nil
    (0, []) (0, [(1, "owner", .pid [])]) (3, []) (3, [(1, "owner", .pid [1])]) (6, [])
    (by simp [acquire]) (update_trace [] 0) (by simp [acquire])
    (by simp [acquire]) (update_trace [1] 3)

/-- Every finite choice list preserves both updates, even when it requests
missing processes or switches after release before the earlier worker returns. -/
theorem contending_multi_wait_all_choices (choices : List ScheduleChoice) :
    let observed := (Result.schedule {} (.wait acquire postUpdate) (fun _ => .wait acquire postUpdate)).run
      {} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.ok Term.nil, 6, []) := by
  have result := Result.two_wait_serial_orders acquire postUpdate acquire postUpdate 0 0 .nil .nil .nil .nil
    (0, []) (0, [(1, "owner", .pid [])]) (3, []) (6, [])
    (0, [(1, "owner", .pid [1])]) (3, []) (6, [])
    (by intro env owner counter heap; simp [acquire, heap, counter, owner])
    (by intro env owner counter heap; simp [acquire, heap, counter, owner])
    (update_exclusive [] [1] 0) (update_full [1] 3)
    (update_exclusive [1] [] 0) (update_full [] 3) choices
  exact result.elim id id

private def localUpdate (value : Nat) : Result Term :=
  .nativeGet fun env => .nativeSet {env with nativeRefCounter := value + 1} (
    .nativeGet fun observed => if observed.nativeRefCounter == value + 1 then
      .wait (release (value + 1)) fun _ => .ok .nil else .error .exhausted)

private theorem local_exclusive (pid peer : PID) (value : Nat) :
    Result.ExclusiveSteps pid peer acquire (localUpdate value)
      (value, [(1, "owner", .pid pid)]) .nil (value + 1, []) := by
  unfold localUpdate
  refine .update _ (.nativeGet fun observed => if observed.nativeRefCounter == value + 1 then
    .wait (release (value + 1)) fun _ => .ok .nil else .error .exhausted)
    _ (value + 1, [(1, "owner", .pid pid)]) _ _ ?_ ?_ ?_
  · intro env _ counter heap
    simp [heap]
  · intro env _ _ heap
    simp [acquire, heap]
  · refine .read _ (.wait (release (value + 1)) fun _ => .ok .nil) _ _ _ ?_ ?_ ?_
    · intro env _ counter heap
      simp [counter]
    · intro env _ _ heap
      simp [acquire, heap]
    · refine .wait _ _ () _ (value + 1, []) _ _ ?_ ?_ (.done _ _)
      · intro env owner counter heap
        simp [release, heap, owner]
      · intro env _ _ heap
        simp [acquire, heap]

/-- Native read/write pairs preserve every arbitrary-choice execution, including
switch requests at release and requests for absent processes or timeouts. -/
theorem local_updates_all_choices (choices : List ScheduleChoice) :
    let observed := (Result.schedule {} (.wait acquire localUpdate)
      (fun _ => .wait acquire localUpdate)).run {} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) = (.ok Term.nil, 2, []) := by
  have second (pid peer : PID) : Result.SharedSteps pid (.wait acquire localUpdate)
      (1, []) .nil (2, []) := by
    refine .wait _ _ 1 _ (1, [(1, "owner", .pid pid)]) _ _ ?_ (local_exclusive pid peer 1).ready
    intro env owner counter heap
    simp [acquire, heap, owner, counter]
  have result := Result.two_wait_serial_orders acquire localUpdate acquire localUpdate 0 0 .nil .nil .nil .nil
    (0, []) (0, [(1, "owner", .pid [])]) (1, []) (2, [])
    (0, [(1, "owner", .pid [1])]) (1, []) (2, [])
    (by intro env owner counter heap; simp [acquire, heap, counter, owner])
    (by intro env owner counter heap; simp [acquire, heap, counter, owner])
    (local_exclusive [] [1] 0) (second [1] []) (local_exclusive [1] [] 0) (second [] [1]) choices
  exact result.elim id id

private def stalled : Result Term :=
  .wait tick fun _ => .wait (fun _ => (none : Option (Unit × Environment))) fun _ => .ok .nil

private theorem stalled_trace (pid peer : PID) (value : Nat) :
    Result.ExclusiveBlocked pid peer acquire stalled (value, [(1, "owner", .pid pid)])
      (value + 1, [(1, "owner", .pid pid)]) := by
  refine .wait _ _ () _ (value + 1, [(1, "owner", .pid pid)]) _ ?_ ?_ ?_
  · intro env owner counter heap
    simp [tick, counter, heap]
  · intro env owner counter heap
    simp [acquire, heap]
  · exact .blocked _ _ _ (by intros; rfl) (by intro env owner counter heap; simp [acquire, heap])

/-- Blocked owners retain their updates and never turn into successful returns,
even when finite choices request the competitor or an ineligible timeout. -/
theorem contending_stall_all_choices (choices : List ScheduleChoice) :
    let observed := (Result.schedule {} (.wait acquire fun _ => stalled)
      (fun _ => .wait acquire fun _ => stalled)).run {} choices
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
        (.deadlock, 1, [(1, "owner", .pid [])]) ∨
    (observed.1, observed.2.nativeRefCounter, observed.2.nativeHeap) =
        (.deadlock, 1, [(1, "owner", .pid [1])]) := by
  exact Result.two_wait_blocked_orders acquire (fun _ => stalled) acquire (fun _ => stalled) 0 0
    (0, []) (0, [(1, "owner", .pid [])]) (1, [(1, "owner", .pid [])])
    (0, [(1, "owner", .pid [1])]) (1, [(1, "owner", .pid [1])])
    (by intro env owner counter heap; simp [acquire, heap, counter, owner])
    (by intro env owner counter heap; simp [acquire, heap, counter, owner])
    (stalled_trace [] [1] 0) (stalled_trace [1] [] 0) choices

/-- Poll readiness alone never makes the wait read-only or pure. -/
theorem wait_is_effectful (poll : Environment → Option (β × Environment)) (next : β → Result α) :
    ¬ Result.IsPure (.wait poll next) ∧ ¬ Result.IsReadOnly (.wait poll next) := by
  simp [Result.IsReadOnly]

end LynxTest.Term.Wait

run_cmd LynxTest.ProofAudit.checkModule `LynxTest.Term.Wait

run_cmd LynxTest.ProofAudit.checkModule `Lynx.Term.Runner
