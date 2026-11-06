module

public import Lynx.Term.Dispatch
public import Lynx.Concurrent
public import Lynx.Concurrent.Termination

/-! Execution of one run. Every step is one of
`Lynx.Concurrent.Config.successors`: signals arrive as soon as they can, the
scheduler choices select which process steps next, and when no process can
step otherwise, a positive timeout expires or the oldest timer fires. So every
execution is a `Lynx.Concurrent.Run`, and it ends because runs do. -/

namespace Lynx.Term.Runner

open Lynx Lynx.Concurrent

/-- Steps are well-founded, so execution can follow them. -/
private instance : WellFoundedRelation (Config α) :=
  ⟨fun next first => ∃ event, Step first event next, Config.terminates⟩

/-- The process a step belongs to. -/
private def owner : Event → Option PID
  | .internal processId | .spawn processId _ | .send processId _ _ | .receive processId _
  | .timeout processId | .exit processId _ | .request processId _ _ => some processId
  | .deliver _ | .bounce _ | .fire _ => none

/-- Whether a computation waits for a message with a positive timeout. -/
private def waitsFinite : Result β → Bool
  | .receive .finite _ _ => true
  | _ => false

/-- Whether a step expires a positive timeout, which only a choice, or the lack
of other steps, takes. -/
private def expires (config : Config α) (event : Event) : Bool :=
  match event, config with
  | .timeout processId, .running _ tasks _ _ =>
      ((tasks.lookup processId).map fun task => waitsFinite task.computation).getD false
  | _, _ => false

/-- A step of a configuration. -/
private abbrev Successor (config : Config α) := { step : Event × Config α // step ∈ config.successors }

/-- The first step whose event satisfies a predicate. -/
private def firstWhere (config : Config α) (keep : Event → Bool) : Option (Successor config) :=
  config.successors.attach.find? fun step => keep step.1.1

/-- A step of a process that does not expire a timeout. -/
private def ordinary (config : Config α) (processId : PID) (event : Event) : Bool :=
  owner event == some processId && !expires config event

/-- The step a choice selects, if available. -/
private def requested (config : Config α) (current : PID) : ScheduleChoice → Option (Successor config)
  | .current => firstWhere config (ordinary config current)
  | .swap processId => firstWhere config (ordinary config processId)
  | .timeout processId => firstWhere config fun event =>
      owner event == some processId && expires config event

/-- Without an available choice: the current process, any process, then a
positive timeout, then a timer. -/
private def fallback (config : Config α) (current : PID) : Option (Successor config) :=
  (firstWhere config (ordinary config current)).orElse fun _ =>
    (firstWhere config fun event => (owner event).isSome && !expires config event).orElse fun _ =>
      (firstWhere config (expires config)).orElse fun _ => firstWhere config fun _ => true

/-- An unavailable choice consumes the next one. -/
private def choose (config : Config α) (current : PID) :
    ScheduleChoice → List ScheduleChoice → List ScheduleChoice × Option (Successor config)
  | preferred, [] =>
      match requested config current preferred with
      | some step => ([], some step)
      | none => ([], fallback config current)
  | preferred, choice :: rest =>
      match requested config current preferred with
      | some step => (choice :: rest, some step)
      | none => choose config current choice rest

/-- Consume one choice at each process-effect boundary. -/
private def schedule : List ScheduleChoice → ScheduleChoice × List ScheduleChoice
  | [] => (.current, [])
  | choice :: rest => (choice, rest)

/-- The root's environment while it is live, and its last one once it ends. -/
private def track (root : PID) (env : Environment) : Config α → Environment
  | .start env _ _ => env
  | .running state _ _ _ => if state.alive root then state.view root else env

/-- Follow steps until none remain, with the root's last environment. -/
private def execute (root : PID) (env : Environment) (config : Config α) (current : PID)
    (preferred : ScheduleChoice) (choices : List ScheduleChoice) : Outcome α × Environment :=
  match firstWhere config (fun event => event matches .deliver _ | .bounce _) with
  | some ⟨(_, next), _⟩ => execute root (track root env next) next current preferred choices
  | none =>
      match choose config current preferred choices with
      | (_, none) => (config.outcome, env)
      | (choices, some ⟨(event, next), _⟩) =>
          let (preferred, choices) := if event matches .internal _ then (.current, choices)
            else schedule choices
          execute root (track root env next) next ((owner event).getD current) preferred choices
termination_by config
decreasing_by all_goals exact ⟨_, ‹_›⟩

/-- Local computations execute structurally; concurrent ones follow the steps
of `Lynx.Concurrent.Config.successors`. -/
def run (computation : Result α) (env : Environment) (choices : List ScheduleChoice) :
    Outcome α × Environment :=
  match computation with
  | .ok value => (.ok value, env)
  | .error exception => (.error exception, env)
  | .get next => run (next env) env choices
  | .set next continuation => run continuation next choices
  | .wait poll next =>
      match poll env with
      | some (value, updated) => run (next value) updated choices
      | none => execute env.currentPid (State.initial env) (.process env.currentPid computation some) none
          false env.currentPid .current choices
  | Result.schedule _ _ _ | .send _ _ _ | .receive _ _ _ | .request _ _ =>
      execute env.currentPid env (.running (State.initial env)
        [(env.currentPid, Task.root computation)] none false) env.currentPid .current choices

/-! ### Soundness -/

private theorem firstWhere_true_none {config : Config α}
    (none : firstWhere config (fun _ => true) = none) : config.successors = [] := by
  simp only [firstWhere, List.find?_eq_none] at none
  cases successors : config.successors with
  | nil => rfl
  | cons head rest =>
    have := none ⟨head, by simp [successors]⟩ (by simp)
    simp at this

private theorem orElse_eq_none {first : Option β} {second : Unit → Option β} :
    first.orElse second = none ↔ first = none ∧ second () = none := by
  cases first <;> simp [Option.orElse]

private theorem choose_none {config : Config α} {current : PID} {preferred : ScheduleChoice}
    {choices remaining : List ScheduleChoice}
    (none : choose config current preferred choices = (remaining, none)) :
    config.successors = [] := by
  induction choices generalizing preferred with
  | nil =>
    simp only [choose] at none
    split at none
    · simp at none
    · simp only [Prod.mk.injEq, fallback, orElse_eq_none] at none
      exact firstWhere_true_none none.2.2.2.2
  | cons choice rest ih =>
    simp only [choose] at none
    split at none
    · simp at none
    · exact ih none

private theorem execute_reaches (root : PID) (config : Config α) :
    ∀ env current preferred choices, ∃ events last, Run config events last ∧
      Terminal last (execute root env config current preferred choices).1 := by
  induction config using Config.terminates.induction with
  | h config ih =>
    intro env current preferred choices
    rw [execute]
    split
    · rename_i next mem _
      obtain ⟨events, last, run, terminal⟩ := ih next ⟨_, mem⟩ _ current preferred choices
      exact ⟨_, last, .step mem run, terminal⟩
    · split
      · rename_i none
        exact ⟨[], config, .refl, .stuck (choose_none none)⟩
      · rename_i event next mem _
        obtain ⟨events, last, run, terminal⟩ := ih next ⟨_, mem⟩ _ _ _ _
        exact ⟨_, last, .step mem run, terminal⟩

private theorem run_reaches (computation : Result α) (env : Environment)
    (choices : List ScheduleChoice) :
    ∃ events last, Concurrent.Run (.start env computation) events last ∧
      Concurrent.Terminal last (run computation env choices).1 := by
  induction computation generalizing env with
  | ok => exact ⟨[], _, .refl, by rw [run]; exact .stuck (by simp [Config.successors, isRequest])⟩
  | error =>
    exact ⟨[], _, .refl, by rw [run]; exact .stuck (by simp [Config.successors, isRequest])⟩
  | get next ih =>
    obtain ⟨events, last, steps, terminal⟩ := ih env env
    exact ⟨_, last, .step (event := .internal env.currentPid) (by simp [Step, Config.successors]) steps,
      by rw [run]; exact terminal⟩
  | set updated next ih =>
    obtain ⟨events, last, steps, terminal⟩ := ih updated
    exact ⟨_, last, .step (event := .internal env.currentPid) (by simp [Step, Config.successors]) steps,
      by rw [run]; exact terminal⟩
  | schedule | send | receive | request =>
    rw [run]
    obtain ⟨events, last, steps, terminal⟩ := execute_reaches env.currentPid _ env env.currentPid
      .current choices
    exact ⟨_, last, .step (event := .internal env.currentPid)
      (by simp [Step, Config.successors, isRequest]) steps, terminal⟩

end Lynx.Term.Runner

public section

namespace Lynx

/-- Execute a computation in an existing environment, consuming the supplied
scheduler choices. Use `Lynx.sequential` to start from a fresh runtime. The
implementation is hidden; the application lemmas below describe its behavior,
and `Lynx.Result.run_reaches` relates it to `Lynx.Concurrent.Step`. Function
values are called through the `Dispatcher` the computation received, so running
needs no program table. -/
def Result.run (computation : Result α) (env : Environment)
    (choices : List ScheduleChoice := []) : Outcome α × Environment :=
  Term.Runner.run computation env choices

instance : CoeFun (Result α) fun _ => Environment → Outcome α × Environment :=
  ⟨fun computation env => computation.run env⟩

namespace Result

@[simp] theorem ok_apply (value : α) (env : Environment) (choices : List ScheduleChoice) :
    (Result.ok value : Result α).run env choices = (.ok value, env) := by
  change Term.Runner.run (.ok value) env choices = _
  rw [Term.Runner.run]

@[simp] theorem error_apply (exception : Exception) (env : Environment)
    (choices : List ScheduleChoice) :
    (Result.error exception : Result α).run env choices = (.error exception, env) := by
  change Term.Runner.run (.error exception) env choices = _
  rw [Term.Runner.run]

@[simp] theorem get_continuation_apply (continuation : Environment → Result α)
    (env : Environment) (choices : List ScheduleChoice) :
    (Result.get continuation).run env choices = (continuation env).run env choices := by
  change Term.Runner.run (.get continuation) env choices = _
  rw [Term.Runner.run]
  rfl

@[simp] theorem set_continuation_apply (next : Environment) (continuation : Result α)
    (env : Environment) (choices : List ScheduleChoice) :
    (Result.set next continuation).run env choices = continuation.run next choices := by
  change Term.Runner.run (.set next continuation) env choices = _
  rw [Term.Runner.run]
  rfl

/-- Every execution, under any scheduler choices, is a run of the transition
system ending in a terminal configuration with the same outcome. -/
theorem run_reaches (computation : Result α) (env : Environment) (choices : List ScheduleChoice) :
    ∃ events last, Concurrent.Run (.start env computation) events last ∧
      Concurrent.Terminal last (computation.run env choices).1 :=
  Term.Runner.run_reaches computation env choices

/-- A ready native wait executes atomically. -/
@[simp] theorem wait_ready_apply (poll : Environment → Option (β × Environment))
    (next : β → Result α) (env updated : Environment) (value : β)
    (ready : poll env = some (value, updated)) :
    (Result.wait poll next) env = next value updated := by
  change Term.Runner.run (.wait poll next) env [] = _
  rw [Term.Runner.run, ready]
  rfl

/-- A finite two-worker trace: the root acquires, the child blocks, the root
releases and finishes, then the child acquires and releases. Poll equations
specify every shared-state transition; neither fairness nor unbounded schedule
coverage is assumed. Process-local state is empty throughout this trace. -/
theorem two_wait_interleave
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentRelease : Environment → Option (δ × Environment)) (parentFinish : δ → Result Term)
    (childRelease : Environment → Option (ε × Environment)) (childFinish : ε → Result Term)
    (parentValue : β) (childValue : γ) (parentReleased : δ) (childReleased : ε)
    (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (saved : List (PID × ProcessState))
        (choices : List ScheduleChoice) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid
         pidCounter := 2
         refCounter := shared.1
         nativeHeap := shared.2
         processes := saved
         schedule := choices } : Environment)
    parentPoll (atState 1 [(2, {})] [.swap 2] s0) =
        some (parentValue, atState 1 [(2, {})] [.swap 2] s1) →
    parentNext parentValue = .wait parentRelease parentFinish →
    childPoll (atState 2 [(1, {})] [] s1) = none →
    parentRelease (atState 1 [(2, {})] [] s1) =
        some (parentReleased, atState 1 [(2, {})] [] s2) →
    parentFinish parentReleased = .ok rootValue →
    childPoll (atState 2 [] [] s2) = some (childValue, atState 2 [] [] s3) →
    childNext childValue = .wait childRelease childFinish →
    childRelease (atState 2 [] [] s3) = some (childReleased, atState 2 [] [] s4) →
    childFinish childReleased = .ok childResult →
    (Result.schedule (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext))
      { refCounter := s0.1, nativeHeap := s0.2, schedule := [.current, .swap 2] } =
      (.ok rootValue, atState 1 [] [] s4) := by
  dsimp only
  intro acquired parent blocked released parentDone childAcquired child childReleased childDone
  change Term.Runner.run _ _ = _
  simp [Term.Runner.run, Term.Runner.execute, Term.Runner.choose, Term.Runner.findReady,
    Term.Runner.findTimeout, Term.Runner.step, Term.Runner.activate, Term.Runner.save,
    Term.Runner.findProcess, Term.Runner.removeProcess, Term.Runner.schedule,
    Term.Runner.restore, Term.Runner.isEmpty,
    acquired, parent, blocked, released, parentDone, childAcquired, child, childReleased, childDone]

/-- The symmetric finite trace: the child acquires first, the root blocks,
then the child finishes before the root acquires and releases. -/
theorem two_wait_interleave_child_first
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentRelease : Environment → Option (δ × Environment)) (parentFinish : δ → Result Term)
    (childRelease : Environment → Option (ε × Environment)) (childFinish : ε → Result Term)
    (parentValue : β) (childValue : γ) (parentReleased : δ) (childReleased : ε)
    (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (saved : List (PID × ProcessState))
        (choices : List ScheduleChoice) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid
         pidCounter := 2
         refCounter := shared.1
         nativeHeap := shared.2
         processes := saved
         schedule := choices } : Environment)
    childPoll (atState 2 [(1, {})] [.swap 1] s0) =
        some (childValue, atState 2 [(1, {})] [.swap 1] s1) →
    childNext childValue = .wait childRelease childFinish →
    parentPoll (atState 1 [(2, {})] [] s1) = none →
    childRelease (atState 2 [(1, {})] [] s1) =
        some (childReleased, atState 2 [(1, {})] [] s2) →
    childFinish childReleased = .ok childResult →
    parentPoll (atState 1 [] [] s2) = some (parentValue, atState 1 [] [] s3) →
    parentNext parentValue = .wait parentRelease parentFinish →
    parentRelease (atState 1 [] [] s3) = some (parentReleased, atState 1 [] [] s4) →
    parentFinish parentReleased = .ok rootValue →
    (Result.schedule (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext))
      { refCounter := s0.1, nativeHeap := s0.2, schedule := [.swap 2, .swap 1] } =
      (.ok rootValue, atState 1 [] [] s4) := by
  dsimp only
  intro acquired child blocked released childDone parentAcquired parent parentReleased parentDone
  change Term.Runner.run _ _ = _
  simp [Term.Runner.run, Term.Runner.execute, Term.Runner.choose, Term.Runner.findReady,
    Term.Runner.findTimeout, Term.Runner.step, Term.Runner.activate, Term.Runner.save,
    Term.Runner.findProcess, Term.Runner.removeProcess, Term.Runner.schedule,
    Term.Runner.restore, Term.Runner.isEmpty,
    acquired, child, blocked, released, childDone, parentAcquired, parent, parentReleased, parentDone]

@[simp] theorem IsPure.ok_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (choices : List ScheduleChoice) (value : α) :
    computation.run env choices = (.ok value, final) ↔ computation = .ok value ∧ env = final := by
  cases computation <;> simp_all

@[simp] theorem IsPure.error_iff (computation : Result α) (pure : IsPure computation)
    (env final : Environment) (choices : List ScheduleChoice) (exception : Exception) :
    computation.run env choices = (.error exception, final) ↔
      computation = .error exception ∧ env = final := by
  cases computation <;> simp_all

end Result

end Lynx
