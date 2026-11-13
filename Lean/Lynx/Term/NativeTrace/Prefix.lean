module
public import Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Serial
import all Lynx.Term.NativeTrace.Scheduled
import all Lynx.Term.Runner
import all Lynx.Concurrent.Reduction

/-! Selection and local registration-prefix execution in the shared scheduler.
The proofs retain arbitrary surrounding tasks and the remaining choice stream;
only the PID uniqueness already required by the scheduler is used. -/

open Lynx Lynx.Concurrent

private theorem ownOwner {state : State} {pid : PID} {task : Concurrent.Task α}
    {transition : Transition α} (mem : transition ∈ task.own state pid) :
    Term.Runner.owner transition.event = some pid := by
  obtain ⟨computation, finish⟩ := task
  cases computation <;> simp only [Concurrent.Task.own] at mem
  all_goals (repeat' split at mem) <;>
    simp_all only [List.mem_singleton, List.not_mem_nil] <;> subst_vars <;> rfl

private theorem successorOwnerUnique {state : State} {pid : PID} {task : Concurrent.Task α}
    {before after : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {transition : Transition α}
    (distinct : (before ++ (pid, task) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (quiet : state.inTransit = []) (own : task.own state pid = [transition])
    {entry : Event × Config α}
    (mem : entry ∈ (Config.running state (before ++ (pid, task) :: after) finished exhausted).successors)
    (owned : Term.Runner.owner entry.1 = some pid) :
    entry = (transition.event, transition.apply before after finished exhausted) := by
  simp only [Config.successors, quiet, deliverable, deliverableFrom, List.filterMap_nil,
    List.append_nil, List.mem_append, List.mem_flatMap, List.mem_map, Prod.exists] at mem
  rcases mem with ⟨before', pid', task', after', split, moved, possible, same⟩ | ⟨timer, _, same⟩
  · simp only [Concurrent.Task.transitions, Concurrent.Task.deliveries, quiet, deliverable,
      deliverableFrom, List.filterMap_nil, List.append_nil] at possible
    cases same
    rw [ownOwner possible, Option.some.injEq] at owned
    subst pid'
    obtain ⟨rfl, rfl, rfl⟩ := split_unique distinct (mem_splits (before := before) (after := after)) split
    rw [own, List.mem_singleton] at possible
    subst possible
    rfl
  · cases same
    contradiction

private theorem selectedUnique {config : Config α} {event : Event} {next : Config α}
    {keep : Event → Bool} (mem : (event, next) ∈ config.successors) (selected : keep event = true)
    (unique : ∀ entry ∈ config.successors, keep entry.1 = true → entry = (event, next)) :
    Term.Runner.firstWhere config keep = some ⟨(event, next), mem⟩ := by
  cases found : Term.Runner.firstWhere config keep with
  | none =>
      have noKeep := (List.find?_eq_none.mp found) ⟨(event, next), mem⟩ (by simp)
      exact False.elim (noKeep selected)
  | some step =>
      have picked := (List.find?_eq_some_iff_append.mp found).1
      exact congrArg some (Subtype.ext (unique step.val step.property picked))

private theorem selectedOwn {state : State} {pid : PID} {task : Concurrent.Task α}
    {before after : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {transition : Transition α}
    (distinct : (before ++ (pid, task) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (quiet : state.inTransit = []) (own : task.own state pid = [transition])
    (owned : Term.Runner.owner transition.event = some pid)
    (nonexpiring : Term.Runner.expires
      (.running state (before ++ (pid, task) :: after) finished exhausted) transition.event = false) :
    ∃ selected, Term.Runner.firstWhere (.running state (before ++ (pid, task) :: after) finished exhausted)
      (Term.Runner.ordinary (.running state (before ++ (pid, task) :: after) finished exhausted) pid) = some selected ∧
      selected.val = (transition.event, transition.apply before after finished exhausted) := by
  have mem := stepOwn (before := before) (after := after) (finished := finished) (exhausted := exhausted)
    (transition := transition) (by rw [own]; exact .head _)
  refine ⟨⟨_, mem⟩, selectedUnique mem (by simp [Term.Runner.ordinary, owned, nonexpiring]) ?_, rfl⟩
  intro entry possible picked
  have owner : Term.Runner.owner entry.1 = some pid := by
    simp only [Term.Runner.ordinary, Bool.and_eq_true, beq_iff_eq] at picked
    exact picked.1
  exact successorOwnerUnique distinct quiet own possible owner


private theorem executeOwn {state : State} {pid : PID} {task : Concurrent.Task α}
    {before after : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool} {transition : Transition α}
    (root current : PID) (env : Environment) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (distinct : (before ++ (pid, task) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (quiet : state.inTransit = []) (own : task.own state pid = [transition])
    (owned : Term.Runner.owner transition.event = some pid)
    (nonexpiring : Term.Runner.expires
      (.running state (before ++ (pid, task) :: after) finished exhausted) transition.event = false)
    (preference : (preferred = .current ∧ current = pid) ∨ preferred = .swap pid) :
    Term.Runner.execute root env (.running state (before ++ (pid, task) :: after) finished exhausted)
      current preferred choices =
      let next := transition.apply before after finished exhausted
      let (preferred, choices) := if Term.Runner.schedulingBoundary
        (.running state (before ++ (pid, task) :: after) finished exhausted) transition.event then
          Term.Runner.schedule choices else (.current, choices)
      Term.Runner.execute root (Term.Runner.track root env next) next pid preferred choices := by
  obtain ⟨⟨⟨event, next⟩, mem⟩, picked, matched⟩ := selectedOwn distinct quiet own owned nonexpiring
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj matched
  have request : Term.Runner.requested
      (.running state (before ++ (pid, task) :: after) finished exhausted) current preferred =
      some ⟨(transition.event, transition.apply before after finished exhausted), mem⟩ := by
    rcases preference with ⟨rfl, rfl⟩ | rfl <;> exact picked
  have noSignal : Term.Runner.firstWhere
      (.running state (before ++ (pid, task) :: after) finished exhausted)
      (fun event => event matches .deliver _ | .bounce _) = none := noDelivery quiet
  rw [Term.Runner.execute]
  split
  · rename_i next mem found
    have impossible := noSignal.symm.trans found
    contradiction
  · cases choices <;> simp only [Term.Runner.choose, request, owned, Option.getD_some]


private theorem distinctTask {pid : PID} {oldTask newTask : Concurrent.Task α}
    {before after : List (PID × Concurrent.Task α)}
    (distinct : (before ++ (pid, oldTask) :: after).Pairwise (fun a b => a.1 ≠ b.1)) :
    (before ++ (pid, newTask) :: after).Pairwise (fun a b => a.1 ≠ b.1) := by
  apply (List.pairwise_map (R := fun a b : PID => a ≠ b) (f := Prod.fst)).mp
  have mapped := (List.pairwise_map (R := fun a b : PID => a ≠ b) (f := Prod.fst)).mpr distinct
  simpa only [List.map_append, List.map_cons, Prod.fst] using mapped

private theorem executeLocalTask {state updated : State} {pid : PID}
    {computation next : Result β} {finish : Except Exception β → Option (Except Exception α)}
    {before after : List (PID × Concurrent.Task α)}
    {finished : Option (Except Exception α)} {exhausted : Bool}
    (root current : PID) (env : Environment) (preferred : ScheduleChoice) (choices : List ScheduleChoice)
    (distinct : (before ++ (pid, ⟨computation, finish⟩) :: after).Pairwise (fun a b => a.1 ≠ b.1))
    (quiet : state.inTransit = [])
    (own : (⟨computation, finish⟩ : Concurrent.Task α).own state pid =
      [{event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]}])
    (nonwaiting : match computation with | .wait .. => False | _ => True)
    (preference : (preferred = .current ∧ current = pid) ∨ preferred = .swap pid) :
    Term.Runner.execute root env
      (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted)
      current preferred choices =
    Term.Runner.execute root (rootEnv root env updated)
      (.running updated (before ++ (pid, ⟨next, finish⟩) :: after) finished exhausted) pid .current choices := by
  have found := lookup_of_mem distinct (show (pid, (⟨computation, finish⟩ : Concurrent.Task α)) ∈
    before ++ (pid, ⟨computation, finish⟩) :: after from by simp)
  have boundary : Term.Runner.schedulingBoundary
      (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted) (.internal pid) = false := by
    cases computation <;> simp_all [Term.Runner.schedulingBoundary]
  simpa [Transition.apply, trackRunning, boundary] using executeOwn
    (before := before) (after := after) (finished := finished) (exhausted := exhausted)
    (transition := {event := .internal pid, state := updated, tasks := [(pid, ⟨next, finish⟩)]})
    root current env preferred choices distinct quiet own rfl rfl preference

private theorem prefixCurrent {pid : PID} {computation residual : Result β}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : Result.RegisteredPrefix pid computation initial types residual final finalTypes)
    (root : PID) (env : Environment) (state : State)
    (before after : List (PID × Concurrent.Task α))
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Option (Except Exception α)) (exhausted : Bool) (choices : List ScheduleChoice)
    (counter : state.nativeRefCounter = initial.1) (heap : state.nativeHeap = initial.2)
    (available : state.nativeResourceTypes = types) (quiet : state.inTransit = [])
    (distinct : (before ++ (pid, ⟨computation, finish⟩) :: after).Pairwise (fun a b => a.1 ≠ b.1)) :
    Term.Runner.execute root (rootEnv root env state)
      (.running state (before ++ (pid, ⟨computation, finish⟩) :: after) finished exhausted) pid .current choices =
    Term.Runner.execute root (rootEnv root env {state with
        nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes})
      (.running {state with nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes}
        (before ++ (pid, ⟨residual, finish⟩) :: after) finished exhausted) pid .current choices := by
  induction trace generalizing state with
  | refl => simp only [← counter, ← heap, ← available]
  | read read body initial final types finalTypes residual ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalTask (updated := state) (next := body) root pid _ .current choices distinct quiet
        (by simp [Concurrent.Task.own, evaluated]) True.intro (.inl ⟨rfl, rfl⟩), rootEnvIdempotent]
      exact ih state counter heap available quiet (distinctTask distinct)
  | update read body initial middle final types middleTypes finalTypes residual ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalTask (updated := state)
        (next := .nativeSet {state.nativeView pid with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes} body)
        root pid _ .current choices distinct quiet (by simp [Concurrent.Task.own, evaluated])
          True.intro (.inl ⟨rfl, rfl⟩), rootEnvIdempotent]
      rw [executeLocalTask (updated := {state with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes})
        (next := body) root pid _ .current choices (distinctTask distinct) quiet
          (by simp [Concurrent.Task.own, storeShared]) True.intro (.inl ⟨rfl, rfl⟩), rootEnvFrame]
      exact ih _ rfl rfl rfl quiet (distinctTask distinct)
  | modify transition next reply initial middle final types middleTypes finalTypes residual ready rest ih =>
      have evaluated := ready (state.nativeView pid) rfl counter heap available
      rw [executeLocalTask (updated := {state with
          nativeRefCounter := middle.1, nativeHeap := middle.2, nativeResourceTypes := middleTypes})
        (next := next reply) root pid _ .current choices distinct quiet
          (by simp [Concurrent.Task.own, evaluated, storeShared]) True.intro (.inl ⟨rfl, rfl⟩), rootEnvFrame]
      exact ih _ rfl rfl rfl quiet (distinctTask distinct)


private theorem spawnPreferred (parent child : Result Term) (shared : Nat × List (Nat × String × Term))
    (types : List String) (preferred : ScheduleChoice) (choices : List ScheduleChoice) :
    (Result.schedule {} child (fun _ => parent)).run (startEnv shared types) (preferred :: choices) =
    Term.Runner.execute [] (rootEnv [] (startEnv shared types) (spawnedState shared types))
      (.running (spawnedState shared types) [([], Concurrent.Task.root parent), ([1], Concurrent.Task.child child)] none false)
      [] preferred choices := by
  change Term.Runner.run _ _ _ = _
  rw [Term.Runner.run]
  change Term.Runner.execute [] (startEnv shared types)
    (.running (State.initial (startEnv shared types))
      [([], Concurrent.Task.root (Result.schedule {} child (fun _ => parent)))] none false)
    [] .current (preferred :: choices) = _
  have own : (Concurrent.Task.root (Result.schedule {} child (fun _ => parent))).own
      (State.initial (startEnv shared types)) [] =
      [{event := .spawn [] [1], state := spawnedState shared types,
        tasks := [([], Concurrent.Task.root parent), ([1], Concurrent.Task.child child)]}] := rfl
  simpa [Transition.apply, trackRunning, Term.Runner.schedulingBoundary, Term.Runner.schedule] using executeOwn
    (before := []) (after := []) (finished := none) (exhausted := false)
    (transition := {
      event := .spawn [] [1], state := spawnedState shared types, tasks := [([], Concurrent.Task.root parent), ([1], Concurrent.Task.child child)]})
    [] [] (startEnv shared types) .current (preferred :: choices) (by simp) rfl own rfl rfl (.inl ⟨rfl, rfl⟩)



namespace Lynx.Result

/-- A local registration/decoding prefix can be normalized in the explicitly
parent-first schedule. Every remaining scheduler choice is retained, and the
residual computation, including any wait, remains in the actual executor. -/
public theorem RegisteredPrefix.spawnCurrent {computation residual : Result Term}
    {initial final : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix [] computation initial types residual final finalTypes)
    (child : Result Term) (choices : List ScheduleChoice) :
    (Result.schedule {} child (fun _ => computation)).run
      {nativeRefCounter := initial.1, nativeHeap := initial.2, nativeResourceTypes := types} (.current :: choices) =
    (Result.schedule {} child (fun _ => residual)).run
      {nativeRefCounter := final.1, nativeHeap := final.2, nativeResourceTypes := finalTypes} (.current :: choices) := by
  change (Result.schedule {} child (fun _ => computation)).run (startEnv initial types) (.current :: choices) =
    (Result.schedule {} child (fun _ => residual)).run (startEnv final finalTypes) (.current :: choices)
  rw [spawnPreferred computation child initial types .current choices, spawnPreferred residual child final finalTypes .current choices]
  simp only [Concurrent.Task.root, Concurrent.Task.child]
  have normalized := prefixCurrent trace [] (startEnv initial types) (spawnedState initial types) []
    [([1], (⟨child, fun _ => none⟩ : Concurrent.Task Term))] some none false choices rfl rfl rfl rfl (by simp)
  simp only [List.nil_append] at normalized
  rw [normalized]
  rfl

end Lynx.Result

