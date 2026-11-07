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

/-- A finite prefix of state reads, state writes and ready waits in one local execution. The residual
computation is retained rather than assumed to finish. Readiness and every
intermediate state are established by the actual operations; this relation does not
inject a crash or choose concurrent scheduler interleavings. -/
inductive ReadyPrefix : Result α → Environment → Result α → Environment → Prop where
  | refl (computation : Result α) (env : Environment) :
      ReadyPrefix computation env computation env
  | get (next : Environment → Result α) (before : Environment)
      (residual : Result α) (after : Environment)
      (rest : ReadyPrefix (next before) before residual after) :
      ReadyPrefix (.get next) before residual after
  | set (middle : Environment) (next : Result α) (before : Environment)
      (residual : Result α) (after : Environment)
      (rest : ReadyPrefix next middle residual after) :
      ReadyPrefix (.set middle next) before residual after
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before middle : Environment)
      (residual : Result α) (after : Environment)
      (ready : poll before = some (reply,middle))
      (rest : ReadyPrefix (next reply) middle residual after) :
      ReadyPrefix (.wait poll next) before residual after

/-- A ready prefix agrees with the existing runner. Completion and its outcome
remain the responsibility of the residual computation. -/
theorem ReadyPrefix.apply {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) :
    computation before = residual after := by
  induction trace with
  | refl => rfl
  | get next before residual after rest ih =>
      rw [get_continuation_apply]
      exact ih
  | set middle next before residual after rest ih =>
      rw [set_continuation_apply]
      exact ih
  | wait poll next reply before middle residual after ready rest ih =>
      rw [wait_ready_apply poll next before middle reply ready]
      exact ih

/-- Extend an existential ready prefix without choosing or rewriting the
residual computation by hand. -/
theorem ReadyPrefix.exists_wait {α β : Type}
    (poll : Environment → Option (β × Environment)) (next : β → Result α)
    (reply : β) (before middle after : Environment)
    (ready : poll before = some (reply,middle))
    (rest : ∃ residual, ReadyPrefix (next reply) middle residual after) :
    ∃ residual, ReadyPrefix (.wait poll next) before residual after := by
  obtain ⟨residual,trace⟩ := rest
  exact ⟨residual,.wait poll next reply before middle residual after ready trace⟩

/-- A caller's continuation can be attached without changing the prefix states. -/
theorem ReadyPrefix.bind {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) (next : α → Result β) :
    ReadyPrefix (computation >>= next) before (residual >>= next) after := by
  induction trace with
  | refl => exact .refl _ _
  | get continuation before residual after rest ih =>
      rw [get_bind]
      exact .get _ _ _ _ ih
  | set middle continuation before residual after rest ih =>
      rw [set_bind]
      exact .set _ _ _ _ _ ih
  | wait poll continuation reply before middle residual after ready rest ih =>
      rw [wait_bind]
      exact .wait poll (fun reply => continuation reply >>= next) reply before middle
        (residual >>= next) after ready ih

/-- Exception handling retains the actual state transitions of a ready prefix.
Verification exhaustion is still governed by `Result.handle` and is never caught. -/
theorem ReadyPrefix.handle {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) (handler : Exception → Result α) :
    ReadyPrefix (Result.handle computation handler) before (Result.handle residual handler) after := by
  induction trace with
  | refl => exact .refl _ _
  | get continuation before residual after rest ih =>
      rw [handle_get]
      exact .get _ _ _ _ ih
  | set middle continuation before residual after rest ih =>
      rw [handle_set]
      exact .set _ _ _ _ _ ih
  | wait poll continuation reply before middle residual after ready rest ih =>
      change ReadyPrefix (.wait poll fun value => Result.handle (continuation value) handler) _ _ _
      exact .wait _ _ _ _ _ _ _ ready ih

/-- A protected computation's prefix composes through its real success and
exception continuations, preserving the boundary of the protected computation. -/
theorem ReadyPrefix.tryWith {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) (next : α → Result β)
    (handler : Exception → Result β) :
    ReadyPrefix (Result.tryWith computation next handler) before
      (Result.tryWith residual next handler) after := by
  unfold Result.tryWith
  exact ((trace.bind _).handle _).bind _

/-- A finite sequence of ready polls in one native execution context. Polls
change only the shared counter and heap; all process and scheduler fields are
framed. This describes the existing wait nodes rather than combining their IO. -/
inductive SharedSteps (pid : PID) : Result α →
    (Nat × List (Nat × String × Term)) → α → (Nat × List (Nat × String × Term)) → Prop where
  | done (value : α) (shared : Nat × List (Nat × String × Term)) :
      SharedSteps pid (.ok value) shared value shared
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.refCounter = before.1 →
        env.nativeHeap = before.2 →
        poll env = some (reply, {env with refCounter := after.1, nativeHeap := after.2}))
      (rest : SharedSteps pid (next reply) after value final) :
      SharedSteps pid (.wait poll next) before value final

/-- Execute a finite ready trace in its owning context, retaining every
non-shared environment field. This does not schedule another process. -/
theorem SharedSteps.apply {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after) (env : Environment)
    (owner : env.currentPid = pid) (counter : env.refCounter = before.1)
    (heap : env.nativeHeap = before.2) :
    computation env = (.ok value, {env with refCounter := after.1, nativeHeap := after.2}) := by
  induction trace generalizing env with
  | done value shared =>
      simp only [Result.ok_apply]
      congr 1
      simp only [← counter, ← heap]
  | wait poll next reply before middle final value ready rest ih =>
      rw [wait_ready_apply poll next env _ reply (ready env owner counter heap)]
      simpa only using ih {env with refCounter := middle.1, nativeHeap := middle.2} owner rfl rfl

/-- Retain a framed native trace as an actual prefix, so its implementation can
compose with caller continuations and adapters without assuming termination. -/
theorem SharedSteps.readyPrefix {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after) (env : Environment)
    (owner : env.currentPid = pid) (counter : env.refCounter = before.1)
    (heap : env.nativeHeap = before.2) :
    ReadyPrefix computation env (.ok value) {env with refCounter := after.1, nativeHeap := after.2} := by
  induction trace generalizing env with
  | done value shared =>
      simp only [← counter,← heap]
      exact .refl _ _
  | wait poll next reply before middle final value ready rest ih =>
      apply ReadyPrefix.wait _ _ _ _ _ _ _ (ready env owner counter heap)
      simpa only using ih {env with refCounter := middle.1,nativeHeap := middle.2} owner rfl rfl

private def traceEnv (pid : PID) (saved : List (PID × ProcessState))
    (shared : Nat × List (Nat × String × Term)) : Environment :=
  { currentPid := pid, pidCounter := 2, processes := saved,
    refCounter := shared.1, nativeHeap := shared.2 }

private theorem sharedSteps_left {α : Type} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps 1 computation before value after)
    (child : Result Term) (finished : Term.Runner.Finished α) :
    Term.Runner.execute 1 (Term.Runner.save (traceEnv 1 [(2, {})] before))
      (.parallel (.process 1 computation some) (.process 2 child (fun _ => none))) finished .current =
    Term.Runner.execute 1 (traceEnv 1 [(2, {})] after)
      (.parallel .empty (.process 2 child (fun _ => none))) (some (.ok value, {})) .current := by
  induction trace with
  | done value shared =>
      rw [Term.Runner.execute]
      simp [Term.Runner.choose, Term.Runner.findReady, Term.Runner.step,
        Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
        Term.Runner.removeProcess, traceEnv]
  | wait poll next reply before middle final value ready rest ih =>
      rw [Term.Runner.execute]
      have polled := ready (traceEnv 1 [(2, {})] before) rfl rfl rfl
      simp only [traceEnv] at polled
      simp [Term.Runner.choose, Term.Runner.findReady, Term.Runner.step,
        Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
        Term.Runner.removeProcess, Term.Runner.schedule, traceEnv, polled]
      exact ih

private theorem sharedSteps_right {α : Type} {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps 2 computation before value after) (rootValue : α) (previous : PID) :
    Term.Runner.execute 1 (traceEnv previous [(2, {})] before)
      (.parallel .empty (.process 2 computation (fun _ => none))) (some (.ok rootValue, {})) .current =
      (.ok rootValue, traceEnv 1 [] after) := by
  induction trace generalizing previous with
  | done value shared =>
      rw [Term.Runner.execute]
      by_cases same : previous = 2
      all_goals simp [Term.Runner.choose, Term.Runner.findReady, Term.Runner.findTimeout,
        Term.Runner.step, Term.Runner.activate, Term.Runner.findProcess,
        Term.Runner.removeProcess, Term.Runner.execute, Term.Runner.restore,
        Term.Runner.isEmpty, traceEnv, same, (eq_comm (a := 2) (b := previous))]
  | wait poll next reply before middle final value ready rest ih =>
      rw [Term.Runner.execute]
      have polled := ready (traceEnv 2 [] before) rfl rfl rfl
      simp only [traceEnv] at polled
      by_cases same : previous = 2
      all_goals
        simp [Term.Runner.choose, Term.Runner.findReady, Term.Runner.findTimeout,
          Term.Runner.step, Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
          Term.Runner.removeProcess, Term.Runner.schedule, traceEnv, polled, same,
          (eq_comm (a := 2) (b := previous))]
        exact ih 2

private theorem choose_single_ready (pool : Term.Runner.Pool α) (pid : PID)
    (env : Environment) (preferred : ScheduleChoice)
    (ready : ∀ choices accept, Term.Runner.findReady {env with schedule := choices} accept pool =
      if accept pid then some pid else none)
    (noTimeout : ∀ choices accept, Term.Runner.findTimeout {env with schedule := choices} accept pool = none) :
    ∃ choices, Term.Runner.choose pool env preferred =
      ({env with schedule := choices}, some (pid, false)) := by
  generalize history : env.schedule = choices
  induction choices generalizing env preferred with
  | nil =>
      have here (accept) := ready [] accept
      have no (accept) := noTimeout [] accept
      simp only [← history] at here no
      cases preferred with
      | current =>
        by_cases same : pid = env.currentPid
        all_goals exact ⟨env.schedule, by cases env; simp_all [Term.Runner.choose]⟩
      | swap requested =>
        by_cases same : pid = env.currentPid <;> by_cases wanted : pid = requested
        all_goals exact ⟨env.schedule, by cases env; simp_all [Term.Runner.choose]⟩
      | timeout requested =>
        by_cases same : pid = env.currentPid
        all_goals exact ⟨env.schedule, by cases env; simp_all [Term.Runner.choose]⟩
  | cons choice rest ih =>
      have here (accept) := ready (choice :: rest) accept
      have no (accept) := noTimeout (choice :: rest) accept
      simp only [← history] at here no
      cases preferred with
      | current =>
        by_cases same : pid = env.currentPid
        · exact ⟨env.schedule, by cases env; simp_all [Term.Runner.choose]⟩
        · obtain ⟨remaining, selected⟩ := ih {env with schedule := rest} choice
            (by simpa using ready) (by simpa using noTimeout) rfl
          exact ⟨remaining, by cases env; simp_all [Term.Runner.choose]⟩
      | swap requested =>
        by_cases same : pid = env.currentPid <;> by_cases wanted : pid = requested
        all_goals exact ⟨env.schedule, by cases env; simp_all [Term.Runner.choose]⟩
      | timeout requested =>
        by_cases same : pid = env.currentPid
        all_goals exact ⟨env.schedule, by cases env; simp_all [Term.Runner.choose]⟩

private def sharedResult (observed : Outcome α × Environment) :
    Outcome α × (Nat × List (Nat × String × Term)) :=
  (observed.1, observed.2.refCounter, observed.2.nativeHeap)

private theorem choose_empty_pair (env : Environment) (preferred : ScheduleChoice) :
    Term.Runner.choose (.parallel .empty .empty : Term.Runner.Pool α) env preferred =
      ({env with schedule := []}, none) := by
  generalize history : env.schedule = choices
  induction choices generalizing env preferred with
  | nil => cases preferred <;> cases env <;>
      simp_all [Term.Runner.choose, Term.Runner.findReady, Term.Runner.findTimeout]
  | cons choice rest ih => cases preferred <;> cases env <;>
      simp_all [Term.Runner.choose, Term.Runner.findReady, Term.Runner.findTimeout]

private theorem execute_empty_pair (root : PID) (env : Environment) (preferred : ScheduleChoice)
    (finished : Term.Runner.Finished α) (value : α)
    (returned : finished.map Prod.fst = some (.ok value)) :
    sharedResult (Term.Runner.execute root env (.parallel .empty .empty) finished preferred) =
      (.ok value, env.refCounter, env.nativeHeap) := by
  cases finished with
  | none => simp at returned
  | some result =>
    rcases result with ⟨reply, process⟩
    simp only [Option.map_some, Option.some.injEq] at returned
    subst reply
    rw [Term.Runner.execute, choose_empty_pair]
    simp [Term.Runner.isEmpty, Term.Runner.restore, sharedResult]

private def solePool (left : Bool) (pid : PID) (computation : Result β)
    (finish : Except Exception β → Option (Except Exception α)) : Term.Runner.Pool α :=
  if left then .parallel (.process pid computation finish) .empty
  else .parallel .empty (.process pid computation finish)

private theorem sharedSteps_sole {α β : Type} {pid : PID} {computation : Result β} {value : β}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after)
    (root : PID) (env : Environment) (preferred : ScheduleChoice) (left : Bool)
    (finish : Except Exception β → Option (Except Exception α))
    (finished : Term.Runner.Finished α) (rootValue : α)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2)
    (returned : (finish (.ok value)).orElse (fun _ => finished.map Prod.fst) = some (.ok rootValue)) :
    sharedResult (Term.Runner.execute root env (solePool left pid computation finish) finished preferred) =
      (.ok rootValue, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.ok value) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp [solePool, Term.Runner.findReady, accepted])
        (by intro choices accept; cases left <;> simp [solePool, Term.Runner.findTimeout])
      rw [Term.Runner.execute, selected]
      cases left <;>
        simp [solePool, Term.Runner.step, Term.Runner.activate, Option.bind_some]
      all_goals
        change _ = (Outcome.ok rootValue, shared.1, shared.2)
        rw [← counter, ← heap]
        apply execute_empty_pair
        cases completed : finish (.ok value) <;> simpa [completed] using returned
  | wait poll next reply before middle final value ready rest ih =>
      have polled (choices : List ScheduleChoice) :
          poll (Term.Runner.activate {env with schedule := choices} pid) =
            some (reply, {Term.Runner.activate {env with schedule := choices} pid with
              refCounter := middle.1, nativeHeap := middle.2}) :=
        ready _ rfl counter heap
      simp only [Term.Runner.activate] at polled
      obtain ⟨choices, selected⟩ := choose_single_ready (solePool left pid (.wait poll next) finish) pid env preferred
        (by intro choices accept; cases left <;> cases accepted : accept pid <;> simp [solePool, Term.Runner.findReady, Term.Runner.activate, polled, accepted])
        (by intro choices accept; cases left <;> simp [solePool, Term.Runner.findTimeout])
      cases choices <;> rw [Term.Runner.execute, selected]
      all_goals cases left <;>
        simp [solePool, Term.Runner.step, polled, Term.Runner.schedule,
          Term.Runner.save, Term.Runner.activate]
      all_goals apply ih <;> first | rfl | exact returned

private theorem choose_pair_ready (pool : Term.Runner.Pool α) (env : Environment)
    (preferred : ScheduleChoice) (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (ready : ∀ accept, Term.Runner.findReady env accept pool =
      if accept 1 then some 1 else if accept 2 then some 2 else none)
    (noTimeout : ∀ accept, Term.Runner.findTimeout env accept pool = none) :
    Term.Runner.choose pool env preferred = (env, some (1, false)) ∨
    Term.Runner.choose pool env preferred = (env, some (2, false)) := by
  rcases current with current | current
  all_goals
    cases preferred with
    | current => simp [Term.Runner.choose, ready, current]
    | timeout requested => simp [Term.Runner.choose, ready, noTimeout, current]
    | swap requested =>
        by_cases one : 1 = requested <;> by_cases two : 2 = requested
        all_goals simp [Term.Runner.choose, ready, current, one, two]

private theorem choose_done_pair {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps 2 computation before value after) (rootValue : Term)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    let pool : Term.Runner.Pool Term := .parallel (.process 1 (.ok rootValue) some)
      (.process 2 computation (fun _ => none))
    Term.Runner.choose pool env preferred = (env, some (1, false)) ∨
    Term.Runner.choose pool env preferred = (env, some (2, false)) := by
  apply choose_pair_ready _ env preferred current
  · intro accept
    cases trace with
    | done value shared => cases a : accept 1 <;> cases b : accept 2 <;>
        simp [Term.Runner.findReady, a, b]
    | wait poll next reply before middle final value ready rest =>
        have polled := ready (Term.Runner.activate env 2) rfl counter heap
        cases a : accept 1 <;> cases b : accept 2 <;> simp [Term.Runner.findReady, a, b, polled]
  · intro accept
    cases trace <;> simp [Term.Runner.findTimeout]

private theorem sharedSteps_pendingRoot {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps 2 computation before value after) (rootValue : Term)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    sharedResult (Term.Runner.execute 1 env
      (.parallel (.process 1 (.ok rootValue) some) (.process 2 computation (fun _ => none))) none preferred) =
      (.ok rootValue, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      rcases choose_done_pair (.done value shared) rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.Runner.execute, selected]
      · simp [Term.Runner.step]
        exact sharedSteps_sole (.done value shared) 1 _ .current false _ _ rootValue counter heap rfl
      · simp [Term.Runner.step]
        exact sharedSteps_sole (.done rootValue shared) 1 _ .current true _ _ rootValue counter heap rfl
  | wait poll next reply before middle final value ready rest ih =>
      have trace := SharedSteps.wait poll next reply before middle final value ready rest
      rcases choose_done_pair trace rootValue env preferred current counter heap with selected | selected
      all_goals rw [Term.Runner.execute, selected]
      · simp [Term.Runner.step]
        exact sharedSteps_sole trace 1 _ .current false _ _ rootValue counter heap rfl
      · have polled := ready (Term.Runner.activate env 2) rfl counter heap
        simp only [Term.Runner.activate] at polled
        cases history : env.schedule
        all_goals
          simp only [history] at polled
          simp [Term.Runner.step, Term.Runner.activate, Term.Runner.save,
            polled, Term.Runner.schedule, history]
          apply ih <;> first | exact Or.inr rfl | rfl

private theorem choose_root_pair {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps 1 computation before value after) (childValue : Term)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    let pool : Term.Runner.Pool Term := .parallel (.process 1 computation some)
      (.process 2 (.ok childValue) (fun _ => none))
    Term.Runner.choose pool env preferred = (env, some (1, false)) ∨
    Term.Runner.choose pool env preferred = (env, some (2, false)) := by
  apply choose_pair_ready _ env preferred current
  · intro accept
    cases trace with
    | done value shared => cases a : accept 1 <;> cases b : accept 2 <;>
        simp [Term.Runner.findReady, a, b]
    | wait poll next reply before middle final value ready rest =>
        have polled := ready (Term.Runner.activate env 1) rfl counter heap
        cases a : accept 1 <;> cases b : accept 2 <;> simp [Term.Runner.findReady, a, b, polled]
  · intro accept
    cases trace <;> simp [Term.Runner.findTimeout]

private theorem sharedSteps_pendingChild {computation : Result Term} {value : Term}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps 1 computation before value after) (childValue : Term)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    sharedResult (Term.Runner.execute 1 env
      (.parallel (.process 1 computation some) (.process 2 (.ok childValue) (fun _ => none))) none preferred) =
      (.ok value, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      exact sharedSteps_pendingRoot (.done childValue shared) value env preferred current counter heap
  | wait poll next reply before middle final value ready rest ih =>
      have trace := SharedSteps.wait poll next reply before middle final value ready rest
      rcases choose_root_pair trace childValue env preferred current counter heap with selected | selected
      all_goals rw [Term.Runner.execute, selected]
      · have polled := ready (Term.Runner.activate env 1) rfl counter heap
        simp only [Term.Runner.activate] at polled
        cases history : env.schedule
        all_goals
          simp only [history] at polled
          simp [Term.Runner.step, Term.Runner.activate, Term.Runner.save,
            polled, Term.Runner.schedule, history]
          apply ih <;> first | exact Or.inl rfl | rfl
      · simp [Term.Runner.step]
        exact sharedSteps_sole trace 1 _ .current true _ _ value counter heap rfl

/-- Ready critical-section polls exclude a peer acquisition before each step.
The final state may release the peer; completion itself performs no shared write.
This evidence is used to reason over all finite scheduler choices. -/
inductive ExclusiveSteps {γ : Type} (pid peer : PID) (peerPoll : Environment → Option (γ × Environment)) :
    Result α → (Nat × List (Nat × String × Term)) → α →
      (Nat × List (Nat × String × Term)) → Prop where
  | done (value : α) (shared : Nat × List (Nat × String × Term)) :
      ExclusiveSteps pid peer peerPoll (.ok value) shared value shared
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.refCounter = before.1 →
        env.nativeHeap = before.2 →
        poll env = some (reply, {env with refCounter := after.1, nativeHeap := after.2}))
      (blocked : ∀ env : Environment, env.currentPid = peer → env.refCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveSteps pid peer peerPoll (next reply) after value final) :
      ExclusiveSteps pid peer peerPoll (.wait poll next) before value final

theorem ExclusiveSteps.ready {pid peer : PID} {peerPoll : Environment → Option (γ × Environment)}
    {computation : Result α} {value : α} {before after : Nat × List (Nat × String × Term)}
    (trace : ExclusiveSteps pid peer peerPoll computation before value after) :
    SharedSteps pid computation before value after := by
  induction trace with
  | done value shared => exact .done value shared
  | wait poll next reply before middle final value ready blocked rest ih =>
      exact .wait poll next reply before middle final value ready ih

/-- A finite ready prefix that ends at a blocked wait while excluding a peer.
Blocking retains the current shared state and is never successful completion. -/
inductive ExclusiveBlocked {γ : Type} (pid peer : PID)
    (peerPoll : Environment → Option (γ × Environment)) :
    Result α → (Nat × List (Nat × String × Term)) →
      (Nat × List (Nat × String × Term)) → Prop where
  | blocked {β : Type} (poll : Environment → Option (β × Environment)) (next : β → Result α)
      (shared : Nat × List (Nat × String × Term))
      (stopped : ∀ env : Environment, env.currentPid = pid → env.refCounter = shared.1 →
        env.nativeHeap = shared.2 → poll env = none)
      (excluded : ∀ env : Environment, env.currentPid = peer → env.refCounter = shared.1 →
        env.nativeHeap = shared.2 → peerPoll env = none) :
      ExclusiveBlocked pid peer peerPoll (.wait poll next) shared shared
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (ready : ∀ env : Environment, env.currentPid = pid → env.refCounter = before.1 →
        env.nativeHeap = before.2 →
        poll env = some (reply, {env with refCounter := after.1, nativeHeap := after.2}))
      (excluded : ∀ env : Environment, env.currentPid = peer → env.refCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveBlocked pid peer peerPoll (next reply) after final) :
      ExclusiveBlocked pid peer peerPoll (.wait poll next) before final

private theorem choose_none_ready (pool : Term.Runner.Pool α) (env : Environment)
    (preferred : ScheduleChoice)
    (ready : ∀ choices accept, Term.Runner.findReady {env with schedule := choices} accept pool = none)
    (noTimeout : ∀ choices accept, Term.Runner.findTimeout {env with schedule := choices} accept pool = none) :
    ∃ choices, Term.Runner.choose pool env preferred = ({env with schedule := choices}, none) := by
  generalize history : env.schedule = choices
  induction choices generalizing env preferred with
  | nil =>
    have here (accept) := ready [] accept
    have no (accept) := noTimeout [] accept
    simp only [← history] at here no
    refine ⟨[], ?_⟩
    cases preferred <;> simp [Term.Runner.choose, here, no]
    all_goals rw [history]; cases env; simp_all
  | cons choice rest ih =>
    have here (accept) := ready (choice :: rest) accept
    have no (accept) := noTimeout (choice :: rest) accept
    simp only [← history] at here no
    obtain ⟨choices, selected⟩ := ih {env with schedule := rest} choice
      (by intros; apply ready) (by intros; apply noTimeout) rfl
    refine ⟨choices, ?_⟩
    cases preferred <;> simp [Term.Runner.choose, here, no]
    all_goals rw [history]; exact selected

private theorem exclusiveSteps_root {β : Type} {computation : Result Term} {value : Term}
    {before middle after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveSteps 1 2 peerPoll computation before value middle)
    (peerTrace : SharedSteps 2 (.wait peerPoll peerNext) middle childValue after)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    sharedResult (Term.Runner.execute 1 env
      (.parallel (.process 1 computation some) (.process 2 (.wait peerPoll peerNext) (fun _ => none))) none preferred) =
      (.ok value, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      exact sharedSteps_pendingRoot peerTrace value env preferred current counter heap
  | wait poll next reply before middle final value ready blocked rest ih =>
      have polled (choices : List ScheduleChoice) :=
        ready (Term.Runner.activate {env with schedule := choices} 1) rfl counter heap
      have excluded (choices : List ScheduleChoice) :=
        blocked (Term.Runner.activate {env with schedule := choices} 2) rfl counter heap
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process 1 (.wait poll next) some) (.process 2 (.wait peerPoll peerNext) (fun _ => none))) 1 env preferred
        (by intro choices accept; cases a : accept 1 <;> cases b : accept 2 <;>
          simp [Term.Runner.findReady, a, b, polled, excluded])
        (by intro choices accept; simp [Term.Runner.findTimeout])
      simp only [Term.Runner.activate] at polled
      cases choices <;> rw [Term.Runner.execute, selected]
      all_goals
        simp [Term.Runner.step, Term.Runner.activate, Term.Runner.save, polled, Term.Runner.schedule]
        apply ih <;> first | exact peerTrace | exact Or.inl rfl | rfl

private theorem exclusiveSteps_child {β : Type} {computation : Result Term} {value : Term}
    {before middle after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveSteps 2 1 peerPoll computation before value middle)
    (peerTrace : SharedSteps 1 (.wait peerPoll peerNext) middle rootValue after)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    sharedResult (Term.Runner.execute 1 env
      (.parallel (.process 1 (.wait peerPoll peerNext) some) (.process 2 computation (fun _ => none))) none preferred) =
      (.ok rootValue, after) := by
  induction trace generalizing env preferred with
  | done value shared =>
      exact sharedSteps_pendingChild peerTrace value env preferred current counter heap
  | wait poll next reply before middle final value ready blocked rest ih =>
      have polled (choices : List ScheduleChoice) :=
        ready (Term.Runner.activate {env with schedule := choices} 2) rfl counter heap
      have excluded (choices : List ScheduleChoice) :=
        blocked (Term.Runner.activate {env with schedule := choices} 1) rfl counter heap
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process 1 (.wait peerPoll peerNext) some) (.process 2 (.wait poll next) (fun _ => none))) 2 env preferred
        (by intro choices accept; cases a : accept 1 <;> cases b : accept 2 <;>
          simp [Term.Runner.findReady, a, b, polled, excluded])
        (by intro choices accept; simp [Term.Runner.findTimeout])
      simp only [Term.Runner.activate] at polled
      cases choices <;> rw [Term.Runner.execute, selected]
      all_goals
        simp [Term.Runner.step, Term.Runner.activate, Term.Runner.save, polled, Term.Runner.schedule]
        apply ih <;> first | exact peerTrace | exact Or.inr rfl | rfl

private theorem exclusiveBlocked_root {β : Type} {computation : Result Term}
    {before after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveBlocked 1 2 peerPoll computation before after)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    sharedResult (Term.Runner.execute 1 env
      (.parallel (.process 1 computation some) (.process 2 (.wait peerPoll peerNext) (fun _ => none))) none preferred) =
      (.deadlock, after) := by
  induction trace generalizing env preferred with
  | blocked poll next shared stopped excluded =>
      have stoppedAll (choices : List ScheduleChoice) :=
        stopped (Term.Runner.activate {env with schedule := choices} 1) rfl counter heap
      have excludedAll (choices : List ScheduleChoice) :=
        excluded (Term.Runner.activate {env with schedule := choices} 2) rfl counter heap
      obtain ⟨choices, selected⟩ := choose_none_ready
        (.parallel (.process 1 (.wait poll next) some)
          (.process 2 (.wait peerPoll peerNext) (fun _ => none))) env preferred
        (by intro choices accept; cases a : accept 1 <;> cases b : accept 2 <;>
          simp [Term.Runner.findReady, a, b, stoppedAll, excludedAll])
        (by intros; simp [Term.Runner.findTimeout])
      rw [Term.Runner.execute, selected]
      simp [Term.Runner.isEmpty, Term.Runner.restore, sharedResult, counter, heap]
  | wait poll next reply before middle final ready blocked rest ih =>
      have polled (choices : List ScheduleChoice) :=
        ready (Term.Runner.activate {env with schedule := choices} 1) rfl counter heap
      have excluded (choices : List ScheduleChoice) :=
        blocked (Term.Runner.activate {env with schedule := choices} 2) rfl counter heap
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process 1 (.wait poll next) some) (.process 2 (.wait peerPoll peerNext) (fun _ => none))) 1 env preferred
        (by intro choices accept; cases a : accept 1 <;> cases b : accept 2 <;>
          simp [Term.Runner.findReady, a, b, polled, excluded])
        (by intro choices accept; simp [Term.Runner.findTimeout])
      simp only [Term.Runner.activate] at polled
      cases choices <;> rw [Term.Runner.execute, selected]
      all_goals
        simp [Term.Runner.step, Term.Runner.activate, Term.Runner.save, polled, Term.Runner.schedule]
        apply ih <;> first | exact Or.inl rfl | rfl

private theorem exclusiveBlocked_child {β : Type} {computation : Result Term}
    {before after : Nat × List (Nat × String × Term)}
    (peerPoll : Environment → Option (β × Environment)) (peerNext : β → Result Term)
    (trace : ExclusiveBlocked 2 1 peerPoll computation before after)
    (env : Environment) (preferred : ScheduleChoice)
    (current : env.currentPid = 1 ∨ env.currentPid = 2)
    (counter : env.refCounter = before.1) (heap : env.nativeHeap = before.2) :
    sharedResult (Term.Runner.execute 1 env
      (.parallel (.process 1 (.wait peerPoll peerNext) some) (.process 2 computation (fun _ => none))) none preferred) =
      (.deadlock, after) := by
  induction trace generalizing env preferred with
  | blocked poll next shared stopped excluded =>
      have stoppedAll (choices : List ScheduleChoice) :=
        stopped (Term.Runner.activate {env with schedule := choices} 2) rfl counter heap
      have excludedAll (choices : List ScheduleChoice) :=
        excluded (Term.Runner.activate {env with schedule := choices} 1) rfl counter heap
      obtain ⟨choices, selected⟩ := choose_none_ready
        (.parallel (.process 1 (.wait peerPoll peerNext) some)
          (.process 2 (.wait poll next) (fun _ => none))) env preferred
        (by intro choices accept; cases a : accept 1 <;> cases b : accept 2 <;>
          simp [Term.Runner.findReady, a, b, stoppedAll, excludedAll])
        (by intros; simp [Term.Runner.findTimeout])
      rw [Term.Runner.execute, selected]
      simp [Term.Runner.isEmpty, Term.Runner.restore, sharedResult, counter, heap]
  | wait poll next reply before middle final ready blocked rest ih =>
      have polled (choices : List ScheduleChoice) :=
        ready (Term.Runner.activate {env with schedule := choices} 2) rfl counter heap
      have excluded (choices : List ScheduleChoice) :=
        blocked (Term.Runner.activate {env with schedule := choices} 1) rfl counter heap
      obtain ⟨choices, selected⟩ := choose_single_ready
        (.parallel (.process 1 (.wait peerPoll peerNext) some) (.process 2 (.wait poll next) (fun _ => none))) 2 env preferred
        (by intro choices accept; cases a : accept 1 <;> cases b : accept 2 <;>
          simp [Term.Runner.findReady, a, b, polled, excluded])
        (by intro choices accept; simp [Term.Runner.findTimeout])
      simp only [Term.Runner.activate] at polled
      cases choices <;> rw [Term.Runner.execute, selected]
      all_goals
        simp [Term.Runner.step, Term.Runner.activate, Term.Runner.save, polled, Term.Runner.schedule]
        apply ih <;> first | exact Or.inr rfl | rfl

/-- Two finite, ready critical sections serialize under every finite scheduler
choice list. Each owner excludes the peer's acquisition until release. Both
possible acquisition orders retain their actual poll transitions and may return
different root results. This theorem
assumes ready IO; it makes no claim about external progress or infinite fairness. -/
theorem two_wait_serial_orders
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootFirst childFirst childSecond rootSecond : Term)
    (initial parentHeld parentReleased parentFinal childHeld childReleased childFinal :
      Nat × List (Nat × String × Term))
    (parentReady : ∀ env : Environment, env.currentPid = 1 → env.refCounter = initial.1 →
      env.nativeHeap = initial.2 → parentPoll env =
        some (parentValue, {env with refCounter := parentHeld.1, nativeHeap := parentHeld.2}))
    (childReady : ∀ env : Environment, env.currentPid = 2 → env.refCounter = initial.1 →
      env.nativeHeap = initial.2 → childPoll env =
        some (childValue, {env with refCounter := childHeld.1, nativeHeap := childHeld.2}))
    (parent : ExclusiveSteps 1 2 childPoll (parentNext parentValue) parentHeld rootFirst parentReleased)
    (childAfter : SharedSteps 2 (.wait childPoll childNext) parentReleased childSecond parentFinal)
    (child : ExclusiveSteps 2 1 parentPoll (childNext childValue) childHeld childFirst childReleased)
    (parentAfter : SharedSteps 1 (.wait parentPoll parentNext) childReleased rootSecond childFinal)
    (choices : List ScheduleChoice) :
    let observed :=
      (Result.schedule (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext))
        {refCounter := initial.1, nativeHeap := initial.2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) = (.ok rootFirst, parentFinal) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) = (.ok rootSecond, childFinal) := by
  let pool : Term.Runner.Pool Term := .parallel (.process 1 (.wait parentPoll parentNext) some)
    (.process 2 (.wait childPoll childNext) (fun _ => none))
  have serial (env : Environment) (preferred : ScheduleChoice)
      (current : env.currentPid = 1 ∨ env.currentPid = 2)
      (counter : env.refCounter = initial.1) (heap : env.nativeHeap = initial.2) :
      sharedResult (Term.Runner.execute 1 env pool none preferred) = (.ok rootFirst, parentFinal) ∨
      sharedResult (Term.Runner.execute 1 env pool none preferred) = (.ok rootSecond, childFinal) := by
    have parentPollReady := parentReady (Term.Runner.activate env 1) rfl counter heap
    have childPollReady := childReady (Term.Runner.activate env 2) rfl counter heap
    have selected := choose_pair_ready pool env preferred current
      (by intro accept; cases a : accept 1 <;> cases b : accept 2 <;>
        simp [pool, Term.Runner.findReady, a, b, parentPollReady, childPollReady])
      (by intro accept; simp [pool, Term.Runner.findTimeout])
    simp only [Term.Runner.activate] at parentPollReady childPollReady
    rcases selected with selected | selected
    · left
      rw [Term.Runner.execute, selected]
      cases history : env.schedule
      all_goals
        simp only [history] at parentPollReady
        simp [pool, Term.Runner.step, parentPollReady, Term.Runner.schedule,
          Term.Runner.save, Term.Runner.activate, history]
        apply exclusiveSteps_root childPoll childNext parent childAfter <;>
          first | exact Or.inl rfl | rfl
    · right
      rw [Term.Runner.execute, selected]
      cases history : env.schedule
      all_goals
        simp only [history] at childPollReady
        simp [pool, Term.Runner.step, childPollReady, Term.Runner.schedule,
          Term.Runner.save, Term.Runner.activate, history]
        apply exclusiveSteps_child parentPoll parentNext child parentAfter <;>
          first | exact Or.inr rfl | rfl
  change sharedResult (Term.Runner.run _ _) = (.ok rootFirst, parentFinal) ∨
    sharedResult (Term.Runner.run _ _) = (.ok rootSecond, childFinal)
  cases choices <;>
    rw [Term.Runner.run, Term.Runner.execute]
  all_goals
    simp [Term.Runner.choose, Term.Runner.findReady, Term.Runner.step,
      Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
      Term.Runner.removeProcess, Term.Runner.schedule]
    apply serial <;> first | exact Or.inl rfl | rfl

/-- Two contenders reach one of their blocked owner states for every finite
scheduler choice list. This establishes a crash observation boundary, not IO
progress: neither blocked execution counts as a successful return. -/
theorem two_wait_blocked_orders
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ)
    (initial parentHeld parentFinal childHeld childFinal :
      Nat × List (Nat × String × Term))
    (parentReady : ∀ env : Environment, env.currentPid = 1 → env.refCounter = initial.1 →
      env.nativeHeap = initial.2 → parentPoll env =
        some (parentValue, {env with refCounter := parentHeld.1, nativeHeap := parentHeld.2}))
    (childReady : ∀ env : Environment, env.currentPid = 2 → env.refCounter = initial.1 →
      env.nativeHeap = initial.2 → childPoll env =
        some (childValue, {env with refCounter := childHeld.1, nativeHeap := childHeld.2}))
    (parent : ExclusiveBlocked 1 2 childPoll (parentNext parentValue) parentHeld parentFinal)
    (child : ExclusiveBlocked 2 1 parentPoll (childNext childValue) childHeld childFinal)
    (choices : List ScheduleChoice) :
    let observed :=
      (Result.schedule (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext))
        {refCounter := initial.1, nativeHeap := initial.2, schedule := choices}
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) = (.deadlock, parentFinal) ∨
    (observed.1, observed.2.refCounter, observed.2.nativeHeap) = (.deadlock, childFinal) := by
  let pool : Term.Runner.Pool Term := .parallel (.process 1 (.wait parentPoll parentNext) some)
    (.process 2 (.wait childPoll childNext) (fun _ => none))
  have serial (env : Environment) (preferred : ScheduleChoice)
      (current : env.currentPid = 1 ∨ env.currentPid = 2)
      (counter : env.refCounter = initial.1) (heap : env.nativeHeap = initial.2) :
      sharedResult (Term.Runner.execute 1 env pool none preferred) = (.deadlock, parentFinal) ∨
      sharedResult (Term.Runner.execute 1 env pool none preferred) = (.deadlock, childFinal) := by
    have parentPollReady := parentReady (Term.Runner.activate env 1) rfl counter heap
    have childPollReady := childReady (Term.Runner.activate env 2) rfl counter heap
    have selected := choose_pair_ready pool env preferred current
      (by intro accept; cases a : accept 1 <;> cases b : accept 2 <;>
        simp [pool, Term.Runner.findReady, a, b, parentPollReady, childPollReady])
      (by intro accept; simp [pool, Term.Runner.findTimeout])
    simp only [Term.Runner.activate] at parentPollReady childPollReady
    rcases selected with selected | selected
    · left
      rw [Term.Runner.execute, selected]
      cases history : env.schedule
      all_goals
        simp only [history] at parentPollReady
        simp [pool, Term.Runner.step, parentPollReady, Term.Runner.schedule,
          Term.Runner.save, Term.Runner.activate, history]
        apply exclusiveBlocked_root childPoll childNext parent <;>
          first | exact Or.inl rfl | rfl
    · right
      rw [Term.Runner.execute, selected]
      cases history : env.schedule
      all_goals
        simp only [history] at childPollReady
        simp [pool, Term.Runner.step, childPollReady, Term.Runner.schedule,
          Term.Runner.save, Term.Runner.activate, history]
        apply exclusiveBlocked_child parentPoll parentNext child <;>
          first | exact Or.inr rfl | rfl
  change sharedResult (Term.Runner.run _ _) = (.deadlock, parentFinal) ∨
    sharedResult (Term.Runner.run _ _) = (.deadlock, childFinal)
  cases choices <;>
    rw [Term.Runner.run, Term.Runner.execute]
  all_goals
    simp [Term.Runner.choose, Term.Runner.findReady, Term.Runner.step,
      Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
      Term.Runner.removeProcess, Term.Runner.schedule]
    apply serial <;> first | exact Or.inl rfl | rfl

/-- Two contending workers retain every IO wait in their finite ready traces.
The root acquires first, a child acquisition is attempted while held, then both
traces execute. This is a concrete schedule theorem, not an arbitrary-schedule
or fairness guarantee. -/
theorem two_wait_interleave_steps
    (parentPoll : Environment → Option (β × Environment)) (parentNext : β → Result Term)
    (childPoll : Environment → Option (γ × Environment)) (childNext : γ → Result Term)
    (parentValue : β) (childValue : γ) (rootValue childResult : Term)
    (s0 s1 s2 s3 s4 : Nat × List (Nat × String × Term)) :
    let atState := fun (pid : PID) (saved : List (PID × ProcessState))
        (choices : List ScheduleChoice) (shared : Nat × List (Nat × String × Term)) =>
      ({ currentPid := pid, pidCounter := 2, processes := saved, schedule := choices,
         refCounter := shared.1, nativeHeap := shared.2 } : Environment)
    parentPoll (atState 1 [(2, {})] [.swap 2] s0) =
      some (parentValue, atState 1 [(2, {})] [.swap 2] s1) →
    SharedSteps 1 (parentNext parentValue) s1 rootValue s2 →
    childPoll (atState 2 [(1, {})] [] s1) = none →
    childPoll (atState 2 [] [] s2) = some (childValue, atState 2 [] [] s3) →
    SharedSteps 2 (childNext childValue) s3 childResult s4 →
    (Result.schedule (.wait childPoll childNext) (fun _ => .wait parentPoll parentNext))
      { refCounter := s0.1, nativeHeap := s0.2, schedule := [.current, .swap 2] } =
      (.ok rootValue, atState 1 [] [] s4) := by
  dsimp only
  intro acquired parent blocked childAcquired child
  change Term.Runner.run _ _ = _
  rw [Term.Runner.run, Term.Runner.execute]
  simp [Term.Runner.choose, Term.Runner.findReady,
    Term.Runner.step, Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
    Term.Runner.removeProcess, Term.Runner.schedule]
  rw [Term.Runner.execute]
  simp [Term.Runner.choose, Term.Runner.findReady,
    Term.Runner.step, Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
    Term.Runner.removeProcess, Term.Runner.schedule, acquired]
  let env := Term.Runner.save (traceEnv 1 [(2, {})] s1)
  let pool : Term.Runner.Pool Term := .parallel
    (.process 1 (parentNext parentValue) some) (.process 2 (.wait childPoll childNext) (fun _ => none))
  have selected : Term.Runner.choose pool env (.swap 2) = Term.Runner.choose pool env .current := by
    simp [Term.Runner.choose, pool, Term.Runner.findReady,
      env, traceEnv, Term.Runner.activate, Term.Runner.save,
      Term.Runner.findProcess, Term.Runner.removeProcess, blocked]
  change Term.Runner.execute 1 env pool none (.swap 2) = _
  have fallback : Term.Runner.execute 1 env pool none (.swap 2) =
      Term.Runner.execute 1 env pool none .current := by
    conv => lhs; rw [Term.Runner.execute]
    conv => rhs; rw [Term.Runner.execute]
    rw [selected]
  rw [fallback]
  rw [sharedSteps_left parent (.wait childPoll childNext) none]
  rw [Term.Runner.execute]
  simp [Term.Runner.choose, Term.Runner.findReady,
    Term.Runner.step, Term.Runner.activate, Term.Runner.save, Term.Runner.findProcess,
    Term.Runner.removeProcess, Term.Runner.schedule, traceEnv, childAcquired]
  exact sharedSteps_right child rootValue 2

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
