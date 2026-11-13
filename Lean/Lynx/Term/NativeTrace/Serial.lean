module
public import Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner

/-! Serial native certificates interpreted by the shared executor. The helpers
select and compose actual scheduler transitions; there is no separate native
interpreter or replacement definition of a first-party computation. -/

open Lynx Lynx.Concurrent

private theorem ownNoDelivery {state : State} {pid : PID} {task : Concurrent.Task α}
    {transition : Transition α} (mem : transition ∈ task.own state pid) :
    (match transition.event with | .deliver _ | .bounce _ => true | _ => false) = false := by
  obtain ⟨computation, finish⟩ := task
  cases computation <;> simp only [Concurrent.Task.own] at mem
  all_goals (repeat' split at mem) <;>
    simp_all only [List.mem_singleton, List.not_mem_nil] <;>
    subst_vars <;> rfl

private theorem noDelivery {state : State} {tasks : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} (quiet : state.inTransit = []) :
    Term.Runner.firstWhere (.running state tasks finished exhausted)
      (fun event => event matches .deliver _ | .bounce _) = none := by
  apply List.find?_eq_none.mpr
  intro step _
  obtain ⟨⟨event, next⟩, possible⟩ := step
  simp only [Config.successors, quiet, deliverable, deliverableFrom, List.filterMap_nil,
    List.append_nil, List.mem_append, List.mem_flatMap, List.mem_map, Prod.exists] at possible
  rcases possible with ⟨before, pid, task, after, split, transition, own, same⟩ | ⟨timer, _, same⟩
  · simp only [Concurrent.Task.transitions, Concurrent.Task.deliveries, quiet,
      deliverable, deliverableFrom, List.filterMap_nil, List.append_nil] at own
    cases same
    simp [ownNoDelivery own]
  · cases same
    simp

private theorem successorsHead {state : State} {pid : PID} {task : Concurrent.Task α}
    {tasks : List (PID × Concurrent.Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    {transition : Transition α} (quiet : state.inTransit = []) (own : task.own state pid = [transition]) :
    ∃ rest, (Config.running state ((pid, task) :: tasks) finished exhausted).successors =
      (transition.event, transition.apply [] tasks finished exhausted) :: rest := by
  simp only [Config.successors, splits, List.flatMap_cons, Concurrent.Task.transitions,
    Concurrent.Task.deliveries, quiet, deliverable, deliverableFrom, List.filterMap_nil,
    own, List.append_nil, List.map_cons, List.map_nil, List.cons_append]
  exact ⟨_, rfl⟩

private theorem selectedHead {config : Config α} {event : Event} {next : Config α}
    {rest : List (Event × Config α)} {keep : Event → Bool}
    (steps : config.successors = (event, next) :: rest) (selected : keep event = true) :
    Term.Runner.firstWhere config keep = some ⟨(event, next), by rw [steps]; exact .head _⟩ := by
  have erased : (Term.Runner.firstWhere config keep).map Subtype.val = some (event, next) := by
    have mapped := (List.find?_map (p := fun pair : Event × Config α => keep pair.1)
      (f := Subtype.val) (l := config.successors.attach)).symm
    calc
      _ = config.successors.find? (fun pair => keep pair.1) := by
        simpa only [List.attach_map_subtype_val, Term.Runner.firstWhere, Function.comp_def] using mapped
      _ = some (event, next) := by
        rw [steps]
        exact List.find?_cons_of_pos selected
  cases found : Term.Runner.firstWhere config keep with
  | none => simp [found] at erased
  | some step =>
      simp only [found, Option.map_some, Option.some.injEq] at erased
      exact congrArg some (Subtype.ext erased)

private theorem executeOwnedHead {state : State} {pid : PID} {task : Concurrent.Task α}
    {tasks : List (PID × Concurrent.Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    {transition : Transition α} (root : PID) (env : Environment)
    (quiet : state.inTransit = []) (own : task.own state pid = [transition])
    (owned : Term.Runner.owner transition.event = some pid)
    (nonexpiring : Term.Runner.expires (.running state ((pid, task) :: tasks) finished exhausted) transition.event = false) :
    Term.Runner.execute root env (.running state ((pid, task) :: tasks) finished exhausted) pid .current [] =
      let next := transition.apply [] tasks finished exhausted
      Term.Runner.execute root (Term.Runner.track root env next) next pid .current [] := by
  obtain ⟨rest, steps⟩ := successorsHead (tasks := tasks) (finished := finished) (exhausted := exhausted) quiet own
  have selected := selectedHead (keep := Term.Runner.ordinary
    (.running state ((pid, task) :: tasks) finished exhausted) pid) steps
    (by simp [Term.Runner.ordinary, owned, nonexpiring])
  have noSignal : Term.Runner.firstWhere (.running state ((pid, task) :: tasks) finished exhausted)
      (fun event => event matches .deliver _ | .bounce _) = none := noDelivery quiet
  rw [Term.Runner.execute]
  split
  · rename_i next mem found
    have impossible := noSignal.symm.trans found
    contradiction
  · simp only [Term.Runner.choose, Term.Runner.requested, selected]
    simp [Term.Runner.schedule, owned]

private def rootEnv (root : PID) (env : Environment) (state : State) : Environment :=
  Term.Runner.track root env (.running state ([] : List (PID × Concurrent.Task Unit)) none false)

private theorem trackRunning (root : PID) (env : Environment) (state : State)
    (tasks : List (PID × Concurrent.Task α)) (finished : Option (Except Exception α)) (exhausted : Bool) :
    Term.Runner.track root env (.running state tasks finished exhausted) = rootEnv root env state := rfl

private theorem rootEnvFrame (root : PID) (env : Environment) (state : State)
    (counter : Nat) (heap : List (Nat × String × Term)) (types : List String) :
    rootEnv root (rootEnv root env state)
      {state with nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types} =
    rootEnv root env {state with nativeRefCounter := counter, nativeHeap := heap, nativeResourceTypes := types} := by
  unfold rootEnv Term.Runner.track
  dsimp only [State.alive]
  by_cases live : (state.processes root).isSome = true <;> simp [live, State.view, State.process]

private theorem rootEnvIdempotent (root : PID) (env : Environment) (state : State) :
    rootEnv root (rootEnv root env state) state = rootEnv root env state := by
  simpa only using rootEnvFrame root env state state.nativeRefCounter state.nativeHeap state.nativeResourceTypes

private theorem executeLocalHead {state updated : State} {pid : PID}
    {computation next : Result β} {finish : Except Exception β → Option (Except Exception α)}
    {tasks : List (PID × Concurrent.Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    (root : PID) (env : Environment) (quiet : state.inTransit = [])
    (own : (⟨computation, finish⟩ : Concurrent.Task α).own state pid =
      [{event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]}]) :
    Term.Runner.execute root env (.running state ((pid, ⟨computation, finish⟩) :: tasks) finished exhausted) pid .current [] =
      Term.Runner.execute root (rootEnv root env updated)
        (.running updated ((pid, ⟨next, finish⟩) :: tasks) finished exhausted) pid .current [] := by
  simpa [Transition.apply, trackRunning] using executeOwnedHead
    (tasks := tasks) (finished := finished) (exhausted := exhausted)
    (transition := {event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]})
    root env quiet own rfl rfl

private theorem sharedSerial {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)}
    (trace : Result.SharedSteps pid computation initial value final) (root : PID) (env : Environment)
    (state : State) (tasks : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) :
    Term.Runner.execute root (rootEnv root env state)
      (.running state ((pid, ⟨computation, finish⟩) :: tasks) finished exhausted) pid .current [] =
    Term.Runner.execute root (rootEnv root env {state with nativeRefCounter := final.1, nativeHeap := final.2})
      (.running {state with nativeRefCounter := final.1, nativeHeap := final.2}
        ((pid, ⟨.ok value, finish⟩) :: tasks) finished exhausted) pid .current [] := by
  induction trace generalizing state with
  | done => simp only [← counter, ← heap]
  | read read body initial final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      rw [executeLocalHead (updated := state) (next := body) root _ quiet
        (by simp [Concurrent.Task.own, evaluated]), rootEnvIdempotent]
      exact ih state counter heap quiet
  | update read body initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      rw [executeLocalHead (updated := state)
        (next := .nativeSet {state.nativeView pid with nativeRefCounter := middle.1, nativeHeap := middle.2} body)
        root _ quiet (by simp [Concurrent.Task.own, evaluated]), rootEnvIdempotent]
      rw [executeLocalHead (updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2})
        (next := body) root _ quiet (by simp [Concurrent.Task.own, storeShared] <;> rfl)]
      rw [rootEnvFrame]
      exact ih _ rfl rfl quiet
  | modify transition next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      rw [executeLocalHead (updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2})
        (next := next reply) root _ quiet (by simp [Concurrent.Task.own, evaluated, storeShared] <;> rfl)]
      rw [rootEnvFrame]
      exact ih _ rfl rfl quiet
  | wait poll next reply initial middle final value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      rw [executeLocalHead (updated := {state with nativeRefCounter := middle.1, nativeHeap := middle.2})
        (next := next reply) root _ quiet (by simp [Concurrent.Task.own, evaluated, storeShared] <;> rfl)]
      rw [rootEnvFrame]
      exact ih _ rfl rfl quiet


private theorem unselectedSingle {config : Config α} {event : Event} {next : Config α}
    {keep : Event → Bool} (steps : config.successors = [(event, next)]) (unselected : keep event ≠ true) :
    Term.Runner.firstWhere config keep = none := by
  apply List.find?_eq_none.mpr
  intro step _
  have same : step.val = (event, next) := by simpa only [steps, List.mem_singleton] using step.property
  simpa only [same] using unselected

private theorem executeUnique {config next : Config α} {event : Event} {pid : PID}
    (root : PID) (env : Environment) (current : PID)
    (steps : config.successors = [(event, next)])
    (owned : Term.Runner.owner event = some pid) (nonexpiring : Term.Runner.expires config event = false) :
    Term.Runner.execute root env config current .current [] =
      Term.Runner.execute root (Term.Runner.track root env next) next pid .current [] := by
  have noSignal : Term.Runner.firstWhere config (fun event => event matches .deliver _ | .bounce _) = none := by
    apply unselectedSingle steps
    cases event <;> simp_all [Term.Runner.owner]
  have chosen : Term.Runner.choose config current .current [] =
      ([], some ⟨(event, next), by rw [steps]; exact .head _⟩) := by
    cases eligible : Term.Runner.ordinary config current event with
    | true =>
        have selected := selectedHead steps eligible
        simp only [Term.Runner.choose, Term.Runner.requested, selected]
    | false =>
        have skipped := unselectedSingle (keep := Term.Runner.ordinary config current) steps (by rw [eligible]; decide)
        have selected := selectedHead (keep := fun event =>
          (Term.Runner.owner event).isSome && !Term.Runner.expires config event) steps
          (by simp [owned, nonexpiring])
        simp only [Term.Runner.choose, Term.Runner.requested, skipped, Term.Runner.fallback,
          selected, Option.orElse_none, Option.orElse_some]
  rw [Term.Runner.execute]
  split
  · rename_i next mem found
    have impossible := noSignal.symm.trans found
    contradiction
  · simp only [chosen]
    simp [Term.Runner.schedule, owned]

private theorem sharedOne {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)}
    (trace : Result.SharedSteps pid computation initial value final)
    (state : State) (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2) :
    ∃ transition, (⟨computation, finish⟩ : Concurrent.Task α).own state pid = [transition] ∧
      Term.Runner.owner transition.event = some pid ∧
      Term.Runner.expires (.running state [(pid, ⟨computation, finish⟩)] finished exhausted) transition.event = false := by
  cases trace with
  | done => exact ⟨_, rfl, rfl, rfl⟩
  | read => exact ⟨_, rfl, rfl, rfl⟩
  | update => exact ⟨_, rfl, rfl, rfl⟩
  | modify => exact ⟨_, rfl, rfl, rfl⟩
  | wait poll next reply initial middle final value ready rest =>
      have evaluated := ready (state.nativeView pid) rfl counter heap
      simp only [Concurrent.Task.own, evaluated]
      exact ⟨_, rfl, rfl, rfl⟩

private def startEnv (shared : Nat × List (Nat × String × Term)) (types : List String := []) : Environment :=
  {nativeRefCounter := shared.1, nativeHeap := shared.2, nativeResourceTypes := types}

private def spawnedState (shared : Nat × List (Nat × String × Term)) (types : List String := []) : State :=
  ((State.initial (startEnv shared types)).spawn []).2

private theorem spawnRun (parent child : Result Term) (shared : Nat × List (Nat × String × Term))
    (types : List String := []) :
    (Result.schedule {} child (fun _ => parent)).run (startEnv shared types) [] =
    Term.Runner.execute [] (rootEnv [] (startEnv shared types) (spawnedState shared types))
      (.running (spawnedState shared types) [([], Concurrent.Task.root parent), ([1], Concurrent.Task.child child)] none false)
      [] .current [] := by
  change Term.Runner.run _ _ _ = _
  rw [Term.Runner.run]
  have steps : (Config.running (State.initial (startEnv shared types))
      [([], Concurrent.Task.root (Result.schedule {} child (fun _ => parent)))] none false).successors =
      [(.spawn [] [1], .running (spawnedState shared types)
        [([], Concurrent.Task.root parent), ([1], Concurrent.Task.child child)] none false)] := by
    rfl
  exact executeUnique [] _ [] steps rfl rfl

private theorem endOk {state : State} {pid : PID} {value : β}
    {finish : Except Exception β → Option (Except Exception α)}
    {tasks : List (PID × Concurrent.Task α)} {finished : Option (Except Exception α)} {exhausted : Bool}
    (root : PID) (env : Environment) (quiet : state.inTransit = []) :
    Term.Runner.execute root env (.running state ((pid, ⟨.ok value, finish⟩) :: tasks) finished exhausted) pid .current [] =
    Term.Runner.execute root (rootEnv root env (state.terminate pid (.atom "normal")))
      (.running (state.terminate pid (.atom "normal")) tasks ((finish (.ok value)).orElse fun _ => finished) exhausted)
      pid .current [] := by
  simpa [Concurrent.Task.ended, Transition.apply, trackRunning] using executeOwnedHead
    (tasks := tasks) (finished := finished) (exhausted := exhausted)
    (task := ⟨.ok value, finish⟩)
    (transition := Concurrent.Task.ended finish (.exit pid (.atom "normal")) state pid (.atom "normal") (.ok value))
    root env quiet rfl rfl rfl

private theorem registeredSerial {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : Result.RegisteredSteps pid computation initial types value final finalTypes)
    (root : PID) (env : Environment) (state : State) (tasks : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (available : state.nativeResourceTypes = types) (quiet : state.inTransit = []) :
    Term.Runner.execute root (rootEnv root env state)
      (.running state ((pid, ⟨computation, finish⟩) :: tasks) finished exhausted) pid .current [] =
    Term.Runner.execute root (rootEnv root env {state with
        nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes})
      (.running {state with nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes}
        ((pid, ⟨.ok value, finish⟩) :: tasks) finished exhausted) pid .current [] := by
  induction trace generalizing state with
  | shared trace types =>
      simpa only [← available] using
        sharedSerial trace root env state tasks finish finished exhausted counter heap quiet
  | read read body initial final types finalTypes value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalHead (updated := state) (next := body) root _ quiet
        (by simp [Concurrent.Task.own, evaluated]), rootEnvIdempotent]
      exact ih state counter heap available quiet
  | update read body initial middle final types middleTypes finalTypes value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalHead (updated := state)
        (next := .nativeSet {state.nativeView pid with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} body)
        root _ quiet (by simp [Concurrent.Task.own, evaluated]), rootEnvIdempotent]
      rw [executeLocalHead (updated := {state with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes})
        (next := body) root _ quiet (by simp [Concurrent.Task.own, storeShared])]
      rw [rootEnvFrame]
      exact ih _ rfl rfl rfl quiet
  | modify transition next reply initial middle final types middleTypes finalTypes value ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalHead (updated := {state with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes})
        (next := next reply) root _ quiet (by simp [Concurrent.Task.own, evaluated, storeShared])]
      rw [rootEnvFrame]
      exact ih _ rfl rfl rfl quiet

private theorem registeredOne {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : Result.RegisteredSteps pid computation initial types value final finalTypes)
    (state : State) (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2) :
    ∃ transition, (⟨computation, finish⟩ : Concurrent.Task α).own state pid = [transition] ∧
      Term.Runner.owner transition.event = some pid ∧
      Term.Runner.expires (.running state [(pid, ⟨computation, finish⟩)] finished exhausted) transition.event = false := by
  cases trace with
  | shared trace => exact sharedOne trace state finish finished exhausted counter heap
  | read => exact ⟨_, rfl, rfl, rfl⟩
  | update => exact ⟨_, rfl, rfl, rfl⟩
  | modify => exact ⟨_, rfl, rfl, rfl⟩

private theorem singleRegisteredCurrent {pid : PID} {computation : Result β} {value : β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : Result.RegisteredSteps pid computation initial types value final finalTypes)
    (root current : PID) (env : Environment) (state : State)
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (quiet : state.inTransit = []) (idle : state.timers = []) :
    Term.Runner.execute root env (.running state [(pid, ⟨computation, finish⟩)] finished exhausted) current .current [] =
    Term.Runner.execute root env (.running state [(pid, ⟨computation, finish⟩)] finished exhausted) pid .current [] := by
  obtain ⟨transition, own, owned, nonexpiring⟩ := registeredOne trace state finish finished exhausted counter heap
  have steps : (Config.running state [(pid, ⟨computation, finish⟩)] finished exhausted).successors =
      [(transition.event, transition.apply [] [] finished exhausted)] := by
    simp [Config.successors, splits, Concurrent.Task.transitions, Concurrent.Task.deliveries,
      quiet, deliverable, deliverableFrom, own, State.firing, idle, firstOfEach]
  exact (executeUnique root env current steps owned nonexpiring).trans
    (executeUnique root env pid steps owned nonexpiring).symm

namespace Lynx.Result

/-- Execute two registration-aware native traces through the shared scheduler.
The empty choice stream keeps the ready parent current, then runs the child.
All native waits and ordinary process-completion transitions are retained. -/
public theorem two_registered_serial_steps (parent child : Result Term) (rootValue childValue : Term)
    (before middle after : Nat × List (Nat × String × Term))
    (types middleTypes finalTypes : List String)
    (parentTrace : RegisteredSteps [] parent before types rootValue middle middleTypes)
    (childTrace : RegisteredSteps [1] child middle middleTypes childValue after finalTypes) :
    (Result.schedule {} child (fun _ => parent)).run {nativeRefCounter := before.1, nativeHeap := before.2, nativeResourceTypes := types} [] =
      (.ok rootValue, {currentPid := [], nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := finalTypes}) := by
  rw [show ({nativeRefCounter := before.1, nativeHeap := before.2, nativeResourceTypes := types} : Environment) = startEnv before types from rfl]
  rw [spawnRun parent child before types]
  let first := spawnedState before types
  let middleState := {first with nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes}
  let parentDone := middleState.terminate [] (.atom "normal")
  let finalState := {parentDone with nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := finalTypes}
  let allDone := finalState.terminate [1] (.atom "normal")
  let parentEnv := rootEnv [] (startEnv before types) middleState
  change Term.Runner.execute [] (rootEnv [] (startEnv before types) first)
    (.running first [([], (⟨parent, some⟩ : Concurrent.Task Term)), ([1], (⟨child, fun _ => none⟩ : Concurrent.Task Term))] none false)
    [] .current [] = _
  rw [registeredSerial parentTrace [] (startEnv before types) first [([1], (⟨child, fun _ => none⟩ : Concurrent.Task Term))] some none false rfl rfl rfl rfl]
  rw [endOk [] parentEnv (by rfl)]
  change Term.Runner.execute [] (rootEnv [] parentEnv parentDone)
    (.running parentDone [([1], (⟨child, fun _ => none⟩ : Concurrent.Task Term))] (some (.ok rootValue)) false) [] .current [] = _
  have quiet : parentDone.inTransit = [] := by
    simp [parentDone, middleState, first, spawnedState, State.spawn, State.initial, State.update,
      State.process, State.terminate, startEnv]
  have idle : parentDone.timers = [] := by
    simp [parentDone, middleState, first, spawnedState, State.spawn, State.initial, State.update,
      State.process, State.terminate, startEnv]
  rw [singleRegisteredCurrent childTrace [] [] _ parentDone (fun _ => none) (some (.ok rootValue)) false rfl rfl quiet idle]
  rw [registeredSerial childTrace [] parentEnv parentDone [] (fun _ => none) (some (.ok rootValue)) false rfl rfl rfl quiet]
  rw [endOk (state := finalState) [] _ (by exact quiet)]
  have stuck : (Config.running allDone ([] : List (PID × Concurrent.Task Term)) (some (.ok rootValue)) false).successors = [] := by
    simp [Config.successors, splits, allDone, finalState, State.terminate, State.process,
      parentDone, middleState, first, spawnedState, startEnv, State.initial, State.spawn, State.update,
      deliverable, deliverableFrom, State.firing, firstOfEach]
  simp only [Option.orElse]
  rw [Term.Runner.execute_stuck _ _ _ stuck]
  simp [Config.outcome, parentEnv, rootEnv, Term.Runner.track, finalState, parentDone, middleState,
    first, spawnedState, startEnv, State.initial, State.spawn, State.update, State.process, State.terminate,
    State.alive, State.view]

/-- Execute two framed native traces in the parent-first serial schedule.
The result includes the child's final shared state, even after the root exits. -/
public theorem two_shared_serial_steps (parent child : Result Term) (rootValue childValue : Term)
    (before middle after : Nat × List (Nat × String × Term))
    (parentTrace : SharedSteps [] parent before rootValue middle)
    (childTrace : SharedSteps [1] child middle childValue after) :
    (Result.schedule {} child (fun _ => parent)).run {nativeRefCounter := before.1, nativeHeap := before.2} [] =
      (.ok rootValue, {currentPid := [], nativeRefCounter := after.1, nativeHeap := after.2}) := by
  exact two_registered_serial_steps parent child rootValue childValue before middle after [] [] []
    (.shared parentTrace []) (.shared childTrace [])

end Lynx.Result
