module

public import Lynx.Term.Runner

public section
namespace Lynx.Result

/-- A finite prefix of local/native state reads, writes and ready waits. The
prefix follows the single-computation `Config.start` semantics and never moves
operations across a spawn. The residual is retained rather than assumed to finish. Readiness and every
intermediate state are established by the actual operations; this relation does not
inject a crash or choose concurrent scheduler interleavings. -/
inductive ReadyPrefix : Result α → Environment → Result α → Environment → Prop where
  | refl (computation : Result α) (env : Environment) :
      ReadyPrefix computation env computation env
  | get (next : Environment → Result α) (before : Environment)
      (residual : Result α) (after : Environment)
      (rest : ReadyPrefix (next before) before residual after) :
      ReadyPrefix (.get next) before residual after
  | nativeGet (next : Environment → Result α) (before : Environment)
      (residual : Result α) (after : Environment)
      (rest : ReadyPrefix (next before) before residual after) :
      ReadyPrefix (.nativeGet next) before residual after
  | set (middle : Environment) (next : Result α) (before : Environment)
      (residual : Result α) (after : Environment)
      (rest : ReadyPrefix next middle residual after) :
      ReadyPrefix (.set middle next) before residual after
  | nativeSet (middle : Environment) (next : Result α) (before : Environment)
      (residual : Result α) (after : Environment)
      (rest : ReadyPrefix next middle residual after) :
      ReadyPrefix (.nativeSet middle next) before residual after
  | nativeModify {β : Type} (transition : Environment → β × Environment)
      (next : β → Result α) (reply : β) (before middle : Environment)
      (residual : Result α) (after : Environment)
      (ready : transition before = (reply,middle))
      (rest : ReadyPrefix (next reply) middle residual after) :
      ReadyPrefix (.nativeModify transition next) before residual after
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before middle : Environment)
      (residual : Result α) (after : Environment)
      (ready : poll before = some (reply,middle))
      (rest : ReadyPrefix (next reply) middle residual after) :
      ReadyPrefix (.wait poll next) before residual after

/-- Compose local prefixes at the same residual and environment. No assumption
about completion or scheduling is introduced by concatenating their steps. -/
theorem ReadyPrefix.trans {computation middle residual : Result α}
    {before midway after : Environment}
    (first : ReadyPrefix computation before middle midway)
    (second : ReadyPrefix middle midway residual after) :
    ReadyPrefix computation before residual after := by
  induction first with
  | refl => exact second
  | get next before middle midway rest ih => exact .get _ _ _ _ (ih second)
  | nativeGet next before middle midway rest ih => exact .nativeGet _ _ _ _ (ih second)
  | set updated next before middle midway rest ih => exact .set _ _ _ _ _ (ih second)
  | nativeSet updated next before middle midway rest ih => exact .nativeSet _ _ _ _ _ (ih second)
  | wait poll next reply before updated middle midway ready rest ih =>
    exact .wait _ _ _ _ _ _ _ ready (ih second)

  | nativeModify transition next reply before updated middle midway ready rest ih =>
    exact .nativeModify _ _ _ _ _ _ _ ready (ih second)

/-- A ready prefix agrees with the existing runner. Completion and its outcome
remain the responsibility of the residual computation. -/
theorem ReadyPrefix.apply {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) :
    computation before = residual after := by
  induction trace with
  | refl => rfl
  | get next before residual after rest ih =>
      exact (get_continuation_apply next before []).trans ih
  | nativeGet next before residual after rest ih =>
      rw [nativeGet_continuation_apply]
      exact ih
  | set middle next before residual after rest ih =>
      exact (set_continuation_apply middle next before []).trans ih
  | nativeSet middle next before residual after rest ih =>
      rw [nativeSet_continuation_apply]
      exact ih
  | wait poll next reply before middle residual after ready rest ih =>
      rw [wait_ready_apply poll next before middle reply ready]
      exact ih

  | nativeModify transition next reply before middle residual after ready rest ih =>
    rw [nativeModify_apply, ready]
    exact ih

/-- A ready prefix preserves an explicit scheduler choice stream. -/
theorem ReadyPrefix.run {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) (choices : List ScheduleChoice) :
    computation.run before choices = residual.run after choices := by
  induction trace with
  | refl => rfl
  | get next before residual after rest ih =>
      rw [get_continuation_apply]
      exact ih
  | nativeGet next before residual after rest ih =>
      rw [nativeGet_continuation_run]
      exact ih
  | set middle next before residual after rest ih =>
      rw [set_continuation_apply]
      exact ih
  | nativeSet middle next before residual after rest ih =>
      rw [nativeSet_continuation_run]
      exact ih
  | wait poll next reply before middle residual after ready rest ih =>
      rw [wait_ready_run poll next before middle reply ready choices]
      exact ih

  | nativeModify transition next reply before middle residual after ready rest ih =>
    rw [nativeModify_run transition next before choices, ready]
    exact ih

/-- A terminal run must take the unique enabled successor. -/
private theorem run_after_single {first next last : Concurrent.Config α}
    {event : Concurrent.Event} {events : List Concurrent.Event} {outcome : Outcome α}
    (successor : first.successors = [(event, next)])
    (run : Concurrent.Run first events last) (terminal : Concurrent.Terminal last outcome) :
    ∃ rest, Concurrent.Run next rest last := by
  cases run with
  | refl =>
      have stuck := terminal.successors_eq_nil
      simp [successor] at stuck
  | step step rest =>
      simp only [Concurrent.Step, successor, List.mem_singleton, Prod.mk.injEq] at step
      obtain ⟨rfl, rfl⟩ := step
      exact ⟨_, rest⟩

/-- A ready native prefix preserves the actual terminal configurations of every
run, including their state and errors. It does not identify all-run verification
with evaluation under a particular scheduler choice stream. -/
theorem ReadyPrefix.terminalRun {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config α} {outcome : Outcome α}
    (run : Concurrent.Run (.start before computation elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) :
    ∃ rest, Concurrent.Run (.start after residual elapsed) rest last := by
  induction trace generalizing events with
  | refl => exact ⟨_, run⟩
  | get next before residual after rest ih =>
      obtain ⟨_, run⟩ := run_after_single rfl run terminal
      exact ih run
  | nativeGet next before residual after rest ih =>
      obtain ⟨_, run⟩ := run_after_single rfl run terminal
      exact ih run
  | set middle next before residual after rest ih =>
      obtain ⟨_, run⟩ := run_after_single rfl run terminal
      exact ih run
  | nativeSet middle next before residual after rest ih =>
      obtain ⟨_, run⟩ := run_after_single rfl run terminal
      exact ih run
  | nativeModify transition next reply before middle residual after ready rest ih =>
      obtain ⟨_, run⟩ := run_after_single
        (next := .start middle (next reply) elapsed) (event := .internal before.currentPid)
        (by simp [Concurrent.Config.successors, ready]) run terminal
      exact ih run
  | wait poll next reply before middle residual after ready rest ih =>
      obtain ⟨_, run⟩ := run_after_single
        (next := .start middle (next reply) elapsed) (event := .internal before.currentPid)
        (by simp [Concurrent.Config.successors, ready]) run terminal
      exact ih run

/-- Finishing a ready prefix proves its return value for every run. The proof
retains every native transition, rather than substituting a single execution. -/
theorem ReadyPrefix.returns {computation : Result α} {before after : Environment} {value : α}
    (trace : ReadyPrefix computation before (.ok value) after) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config α} {outcome : Outcome α}
    (run : Concurrent.Run (.start before computation elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) : outcome = .ok value := by
  obtain ⟨_, rest⟩ := trace.terminalRun elapsed run terminal
  cases rest with
  | refl => exact terminal.outcome_eq.symm
  | step step _ => simp [Concurrent.Step, Concurrent.Config.successors, Concurrent.isRequest] at step

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
  | nativeGet continuation before residual after rest ih =>
      rw [nativeGet_bind]
      exact .nativeGet _ _ _ _ ih
  | set middle continuation before residual after rest ih =>
      rw [set_bind]
      exact .set _ _ _ _ _ ih
  | nativeSet middle continuation before residual after rest ih =>
      rw [nativeSet_bind]
      exact .nativeSet _ _ _ _ _ ih
  | wait poll continuation reply before middle residual after ready rest ih =>
      rw [wait_bind]
      exact .wait poll (fun reply => continuation reply >>= next) reply before middle
        (residual >>= next) after ready ih

  | nativeModify transition continuation reply before middle residual after ready rest ih =>
    rw [nativeModify_bind]
    exact .nativeModify _ _ _ _ _ _ _ ready ih

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
  | nativeGet continuation before residual after rest ih =>
      rw [handle_nativeGet]
      exact .nativeGet _ _ _ _ ih
  | set middle continuation before residual after rest ih =>
      rw [handle_set]
      exact .set _ _ _ _ _ ih
  | nativeSet middle continuation before residual after rest ih =>
      rw [handle_nativeSet]
      exact .nativeSet _ _ _ _ _ ih
  | wait poll continuation reply before middle residual after ready rest ih =>
      change ReadyPrefix (.wait poll fun value => Result.handle (continuation value) handler) _ _ _
      exact .wait _ _ _ _ _ _ _ ready ih

  | nativeModify transition continuation reply before middle residual after ready rest ih =>
    rw [handle_nativeModify]
    exact .nativeModify _ _ _ _ _ _ _ ready ih

/-- A protected computation's prefix composes through its real success and
exception continuations, preserving the boundary of the protected computation. -/
theorem ReadyPrefix.tryWith {computation residual : Result α} {before after : Environment}
    (trace : ReadyPrefix computation before residual after) (next : α → Result β)
    (handler : Exception → Result β) :
    ReadyPrefix (Result.tryWith computation next handler) before
      (Result.tryWith residual next handler) after := by
  unfold Result.tryWith
  exact ((trace.bind _).handle _).bind _

/-- A finite native trace of framed reads, read/write pairs and ready polls.
Only the shared counter and heap change; process and scheduler fields remain
framed. The trace retains the actual get/set and wait nodes. -/
inductive SharedSteps (pid : PID) : Result α →
    (Nat × List (Nat × String × Term)) → α → (Nat × List (Nat × String × Term)) → Prop where
  | done (value : α) (shared : Nat × List (Nat × String × Term)) :
      SharedSteps pid (.ok value) shared value shared
  | read (read : Environment → Result α) (body : Result α)
      (before final : Nat × List (Nat × String × Term)) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → read env = body)
      (rest : SharedSteps pid body before value final) :
      SharedSteps pid (.nativeGet read) before value final
  | update (read : Environment → Result α) (body : Result α)
      (before after final : Nat × List (Nat × String × Term)) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        read env = .nativeSet {env with nativeRefCounter := after.1, nativeHeap := after.2} body)
      (rest : SharedSteps pid body after value final) :
      SharedSteps pid (.nativeGet read) before value final
  | modify {β : Type} (transition : Environment → β × Environment)
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        transition env = (reply, {env with nativeRefCounter := after.1, nativeHeap := after.2}))
      (rest : SharedSteps pid (next reply) after value final) :
      SharedSteps pid (.nativeModify transition next) before value final
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        poll env = some (reply, {env with nativeRefCounter := after.1, nativeHeap := after.2}))
      (rest : SharedSteps pid (next reply) after value final) :
      SharedSteps pid (.wait poll next) before value final

/-- Execute a finite ready trace in its owning context, retaining every
non-shared environment field. This does not schedule another process. -/
theorem SharedSteps.apply {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after) (env : Environment)
    (owner : env.currentPid = pid) (counter : env.nativeRefCounter = before.1)
    (heap : env.nativeHeap = before.2) :
    computation env = (.ok value, {env with nativeRefCounter := after.1, nativeHeap := after.2}) := by
  induction trace generalizing env with
  | done value shared =>
      simp only [Result.ok_apply]
      congr 1
      simp only [← counter, ← heap]
  | read read body before final value ready rest ih =>
      rw [nativeGet_continuation_apply, ready env owner counter heap]
      exact ih env owner counter heap
  | update read body before middle final value ready rest ih =>
      rw [nativeGet_continuation_apply, ready env owner counter heap, nativeSet_continuation_apply]
      exact ih _ owner rfl rfl
  | wait poll next reply before middle final value ready rest ih =>
      rw [wait_ready_apply poll next env _ reply (ready env owner counter heap)]
      simpa only using ih {env with nativeRefCounter := middle.1, nativeHeap := middle.2} owner rfl rfl

  | modify transition next reply before middle final value ready rest ih =>
      rw [nativeModify_apply, ready env owner counter heap]
      exact ih _ owner rfl rfl

/-- Retain a framed native trace as an actual prefix, so its implementation can
compose with caller continuations and adapters without assuming termination. -/
theorem SharedSteps.readyPrefix {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after) (env : Environment)
    (owner : env.currentPid = pid) (counter : env.nativeRefCounter = before.1)
    (heap : env.nativeHeap = before.2) :
    ReadyPrefix computation env (.ok value) {env with nativeRefCounter := after.1, nativeHeap := after.2} := by
  induction trace generalizing env with
  | done value shared =>
      simp only [← counter,← heap]
      exact .refl _ _
  | read read body before final value ready rest ih =>
      apply ReadyPrefix.nativeGet
      rw [ready env owner counter heap]
      exact ih env owner counter heap
  | update read body before middle final value ready rest ih =>
      apply ReadyPrefix.nativeGet
      rw [ready env owner counter heap]
      apply ReadyPrefix.nativeSet
      exact ih _ owner rfl rfl
  | wait poll next reply before middle final value ready rest ih =>
      apply ReadyPrefix.wait _ _ _ _ _ _ _ (ready env owner counter heap)
      simpa only using ih {env with nativeRefCounter := middle.1,nativeHeap := middle.2} owner rfl rfl

  | modify transition next reply before middle final value ready rest ih =>
      apply ReadyPrefix.nativeModify _ _ _ _ _ _ _ (ready env owner counter heap)
      exact ih _ owner rfl rfl

/-- A successful native trace composes with its actual caller continuation. -/
theorem SharedSteps.bind {pid : PID} {computation : Result α} {value : α}
    {before middle after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value middle) (next : α → Result β)
    (tail : SharedSteps pid (next value) middle answer after) :
    SharedSteps pid (computation >>= next) before answer after := by
  induction trace with
  | done => simpa only [Result.ok_bind] using tail
  | read read body before final value ready rest ih =>
      rw [Result.nativeGet_bind]
      refine .read _ (body >>= next) _ _ _ ?_ (ih tail)
      intro env owner count heap
      rw [ready env owner count heap]
  | update read body before middle final value ready rest ih =>
      rw [Result.nativeGet_bind]
      refine .update _ (body >>= next) _ _ _ _ ?_ (ih tail)
      intro env owner count heap
      rw [ready env owner count heap, Result.nativeSet_bind]
  | wait poll nextStep reply before middle final value ready rest ih =>
      rw [Result.wait_bind]
      exact .wait _ _ _ _ _ _ _ ready (ih tail)

  | modify transition nextStep reply before middle final value ready rest ih =>
      rw [nativeModify_bind]
      exact .modify _ _ _ _ _ _ _ ready (ih tail)

/-- Exception conversion preserves a successful scheduled native trace. -/
theorem SharedSteps.handle {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)}
    (trace : SharedSteps pid computation before value after) (handler : Exception → Result α) :
    SharedSteps pid (Result.handle computation handler) before value after := by
  induction trace with
  | done value shared => simpa only [Result.handle] using SharedSteps.done (pid := pid) value shared
  | read read body before final value ready rest ih =>
      simp only [Result.handle]
      refine .read _ (Result.handle body handler) _ _ _ ?_ ih
      intro env owner count heap
      rw [ready env owner count heap]
  | update read body before middle final value ready rest ih =>
      simp only [Result.handle]
      refine .update _ (Result.handle body handler) _ _ _ _ ?_ ih
      intro env owner count heap
      rw [ready env owner count heap]
      rfl
  | wait poll next reply before middle final value ready rest ih =>
      simp only [Result.handle]
      exact .wait _ _ _ _ _ _ _ ready ih

  | modify transition next reply before middle final value ready rest ih =>
      rw [handle_nativeModify]
      exact .modify _ _ _ _ _ _ _ ready ih

/-- A native shared trace preceded by local registration or decoding steps.
The resource-type registry is explicit in the state; process-local fields and
scheduler choices remain framed. The shared constructor reuses `SharedSteps`,
including its actual wait nodes, rather than treating execution as atomic. -/
inductive RegisteredSteps (pid : PID) : Result α →
    (Nat × List (Nat × String × Term)) → List String → α →
    (Nat × List (Nat × String × Term)) → List String → Prop where
  | shared (trace : SharedSteps pid computation before value after) (types : List String) :
      RegisteredSteps pid computation before types value after types
  | read (read : Environment → Result α) (body : Result α)
      (before final : Nat × List (Nat × String × Term)) (types finalTypes : List String) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → env.nativeResourceTypes = types → read env = body)
      (rest : RegisteredSteps pid body before types value final finalTypes) :
      RegisteredSteps pid (.nativeGet read) before types value final finalTypes
  | update (read : Environment → Result α) (body : Result α)
      (before after final : Nat × List (Nat × String × Term))
      (types afterTypes finalTypes : List String) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → env.nativeResourceTypes = types →
        read env = .nativeSet {env with
          nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := afterTypes} body)
      (rest : RegisteredSteps pid body after afterTypes value final finalTypes) :
      RegisteredSteps pid (.nativeGet read) before types value final finalTypes
  | modify {β : Type} (transition : Environment → β × Environment) (next : β → Result α) (reply : β)
      (before after final : Nat × List (Nat × String × Term))
      (types afterTypes finalTypes : List String) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → env.nativeResourceTypes = types →
        transition env = (reply, {env with
          nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := afterTypes}))
      (rest : RegisteredSteps pid (next reply) after afterTypes value final finalTypes) :
      RegisteredSteps pid (.nativeModify transition next) before types value final finalTypes

/-- Local native steps ending at an unevaluated continuation. Only synchronous state
nodes are consumed: reaching a wait leaves its poll to the actual scheduler.
The registry, counter and heap are explicit; all process fields stay framed. -/
inductive RegisteredPrefix (pid : PID) : Result α →
    (Nat × List (Nat × String × Term)) → List String → Result α →
    (Nat × List (Nat × String × Term)) → List String → Prop where
  | refl (computation : Result α) (shared : Nat × List (Nat × String × Term)) (types : List String) :
      RegisteredPrefix pid computation shared types computation shared types
  | read (read : Environment → Result α) (body : Result α)
      (before final : Nat × List (Nat × String × Term)) (types finalTypes : List String) (residual : Result α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → env.nativeResourceTypes = types → read env = body)
      (rest : RegisteredPrefix pid body before types residual final finalTypes) :
      RegisteredPrefix pid (.nativeGet read) before types residual final finalTypes
  | update (read : Environment → Result α) (body : Result α)
      (before after final : Nat × List (Nat × String × Term))
      (types afterTypes finalTypes : List String) (residual : Result α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → env.nativeResourceTypes = types →
        read env = .nativeSet {env with
          nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := afterTypes} body)
      (rest : RegisteredPrefix pid body after afterTypes residual final finalTypes) :
      RegisteredPrefix pid (.nativeGet read) before types residual final finalTypes
  | modify {β : Type} (transition : Environment → β × Environment) (next : β → Result α) (reply : β)
      (before after final : Nat × List (Nat × String × Term))
      (types afterTypes finalTypes : List String) (residual : Result α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → env.nativeResourceTypes = types →
        transition env = (reply, {env with
          nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := afterTypes}))
      (rest : RegisteredPrefix pid (next reply) after afterTypes residual final finalTypes) :
      RegisteredPrefix pid (.nativeModify transition next) before types residual final finalTypes

/-- Concatenate only local steps; the final residual remains unevaluated. -/
theorem RegisteredPrefix.trans {pid : PID} {computation middle residual : Result α}
    {before midway after : Nat × List (Nat × String × Term)} {types middleTypes finalTypes : List String}
    (first : RegisteredPrefix pid computation before types middle midway middleTypes)
    (second : RegisteredPrefix pid middle midway middleTypes residual after finalTypes) :
    RegisteredPrefix pid computation before types residual after finalTypes := by
  induction first with
  | refl => exact second
  | read read body before midway types middleTypes middle ready rest ih =>
      exact .read _ _ _ _ _ _ _ ready (ih second)
  | update read body before next midway types nextTypes middleTypes middle ready rest ih =>
      exact .update _ _ _ _ _ _ _ _ _ ready (ih second)

  | modify transition next reply before updated midway types updatedTypes middleTypes middle ready rest ih =>
    exact .modify _ _ _ _ _ _ _ _ _ _ ready (ih second)

/-- Attach an actual continuation without consuming any of its scheduler waits. -/
theorem RegisteredPrefix.bind {pid : PID} {computation residual : Result α}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix pid computation before types residual after finalTypes)
    (next : α → Result β) :
    RegisteredPrefix pid (computation >>= next) before types (residual >>= next) after finalTypes := by
  induction trace with
  | refl => exact .refl _ _ _
  | read read body before final types finalTypes residual ready rest ih =>
      rw [Result.nativeGet_bind]
      refine .read _ _ _ _ _ _ _ ?_ ih
      intro env actor refs heap registered
      rw [ready env actor refs heap registered]
  | update read body before middle final types middleTypes finalTypes residual ready rest ih =>
      rw [Result.nativeGet_bind]
      refine .update _ _ _ _ _ _ _ _ _ ?_ ih
      intro env actor refs heap registered
      rw [ready env actor refs heap registered, Result.nativeSet_bind]

  | modify transition continuation reply before middle final types middleTypes finalTypes residual ready rest ih =>
    rw [nativeModify_bind]
    exact .modify _ _ _ _ _ _ _ _ _ _ ready ih

/-- Preserve exception conversion at the residual, including its wait nodes. -/
theorem RegisteredPrefix.handle {pid : PID} {computation residual : Result α}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredPrefix pid computation before types residual after finalTypes)
    (handler : Exception → Result α) :
    RegisteredPrefix pid (Result.handle computation handler) before types
      (Result.handle residual handler) after finalTypes := by
  induction trace with
  | refl => exact .refl _ _ _
  | read read body before final types finalTypes residual ready rest ih =>
      simp only [Result.handle]
      refine .read _ _ _ _ _ _ _ ?_ ih
      intro env actor refs heap registered
      rw [ready env actor refs heap registered]
  | update read body before middle final types middleTypes finalTypes residual ready rest ih =>
      simp only [Result.handle]
      refine .update _ _ _ _ _ _ _ _ _ ?_ ih
      intro env actor refs heap registered
      rw [ready env actor refs heap registered]
      rfl

  | modify transition next reply before middle final types middleTypes finalTypes residual ready rest ih =>
    rw [handle_nativeModify]
    exact .modify _ _ _ _ _ _ _ _ _ _ ready ih

/-- Join a local prefix to its proven remaining implementation. -/
theorem RegisteredPrefix.thenSteps {pid : PID} {computation residual : Result α} {value : α}
    {before middle after : Nat × List (Nat × String × Term)}
    {types middleTypes finalTypes : List String}
    (first : RegisteredPrefix pid computation before types residual middle middleTypes)
    (rest : RegisteredSteps pid residual middle middleTypes value after finalTypes) :
    RegisteredSteps pid computation before types value after finalTypes := by
  induction first with
  | refl => exact rest
  | read read body before middle types middleTypes residual ready tail ih =>
      exact .read _ _ _ _ _ _ _ ready (ih rest)
  | update read body before next middle types nextTypes middleTypes residual ready tail ih =>
      exact .update _ _ _ _ _ _ _ _ _ ready (ih rest)

  | modify transition next reply before updated middle types updatedTypes middleTypes residual ready tail ih =>
    exact .modify _ _ _ _ _ _ _ _ _ _ ready (ih rest)

/-- Registration-aware prefixes compose through the actual implementation and
retain every non-native environment field. -/
theorem RegisteredSteps.readyPrefix {pid : PID} {computation : Result α} {value : α}
    {before after : Nat × List (Nat × String × Term)} {types finalTypes : List String}
    (trace : RegisteredSteps pid computation before types value after finalTypes)
    (env : Environment) (owner : env.currentPid = pid) (counter : env.nativeRefCounter = before.1)
    (heap : env.nativeHeap = before.2) (available : env.nativeResourceTypes = types) :
    ReadyPrefix computation env (.ok value) {env with
      nativeRefCounter := after.1, nativeHeap := after.2, nativeResourceTypes := finalTypes} := by
  induction trace generalizing env with
  | shared trace types =>
      simpa only [← available] using trace.readyPrefix env owner counter heap
  | read read body before final types finalTypes value ready rest ih =>
      apply ReadyPrefix.nativeGet
      rw [ready env owner counter heap available]
      exact ih env owner counter heap available
  | update read body before middle final types middleTypes finalTypes value ready rest ih =>
      apply ReadyPrefix.nativeGet
      rw [ready env owner counter heap available]
      apply ReadyPrefix.nativeSet
      exact ih _ owner rfl rfl rfl

  | modify transition next reply before middle final types middleTypes finalTypes value ready rest ih =>
    apply ReadyPrefix.nativeModify _ _ _ _ _ _ _ (ready env owner counter heap available)
    exact ih _ owner rfl rfl rfl

/-- Local reads, framed updates and ready polls exclude a peer before each step.
The final state may release the peer; completion itself performs no shared write.
This evidence is used to reason over all finite scheduler choices. -/
inductive ExclusiveSteps {γ : Type} (pid peer : PID) (peerPoll : Environment → Option (γ × Environment)) :
    Result α → (Nat × List (Nat × String × Term)) → α →
      (Nat × List (Nat × String × Term)) → Prop where
  | done (value : α) (shared : Nat × List (Nat × String × Term)) :
      ExclusiveSteps pid peer peerPoll (.ok value) shared value shared
  | read (read : Environment → Result α) (body : Result α)
      (before final : Nat × List (Nat × String × Term)) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → read env = body)
      (blocked : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveSteps pid peer peerPoll body before value final) :
      ExclusiveSteps pid peer peerPoll (.nativeGet read) before value final
  | update (read : Environment → Result α) (body : Result α)
      (before after final : Nat × List (Nat × String × Term)) (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        read env = .nativeSet {env with nativeRefCounter := after.1, nativeHeap := after.2} body)
      (blocked : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveSteps pid peer peerPoll body after value final) :
      ExclusiveSteps pid peer peerPoll (.nativeGet read) before value final
  | modify {β : Type} (transition : Environment → β × Environment)
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        transition env = (reply, {env with nativeRefCounter := after.1, nativeHeap := after.2}))
      (blocked : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveSteps pid peer peerPoll (next reply) after value final) :
      ExclusiveSteps pid peer peerPoll (.nativeModify transition next) before value final
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (value : α)
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        poll env = some (reply, {env with nativeRefCounter := after.1, nativeHeap := after.2}))
      (blocked : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveSteps pid peer peerPoll (next reply) after value final) :
      ExclusiveSteps pid peer peerPoll (.wait poll next) before value final

theorem ExclusiveSteps.ready {pid peer : PID} {peerPoll : Environment → Option (γ × Environment)}
    {computation : Result α} {value : α} {before after : Nat × List (Nat × String × Term)}
    (trace : ExclusiveSteps pid peer peerPoll computation before value after) :
    SharedSteps pid computation before value after := by
  induction trace with
  | done value shared => exact .done value shared
  | read read body before final value ready blocked rest ih =>
      exact .read read body before final value ready ih
  | update read body before middle final value ready blocked rest ih =>
      exact .update read body before middle final value ready ih
  | wait poll next reply before middle final value ready blocked rest ih =>
      exact .wait poll next reply before middle final value ready ih

  | modify transition next reply before middle final value ready blocked rest ih =>
      exact .modify _ _ _ _ _ _ _ ready ih

/-- Compose an exclusive trace with its checked continuation. -/
theorem ExclusiveSteps.bind {pid peer : PID} {peerPoll : Environment → Option (γ × Environment)} {computation : Result α} {value : α}
    {before middle after : Nat × List (Nat × String × Term)}
    (trace : ExclusiveSteps pid peer peerPoll computation before value middle) (next : α → Result β)
    (tail : ExclusiveSteps pid peer peerPoll (next value) middle answer after) :
    ExclusiveSteps pid peer peerPoll (computation >>= next) before answer after := by
  induction trace with
  | done => simpa only [Result.ok_bind] using tail
  | read read body before final value ready blocked rest ih =>
      rw [Result.nativeGet_bind]
      refine .read _ (body >>= next) _ _ _ ?_ blocked (ih tail)
      intro env owner count heap
      rw [ready env owner count heap]
  | update read body before middle final value ready blocked rest ih =>
      rw [Result.nativeGet_bind]
      refine .update _ (body >>= next) _ _ _ _ ?_ blocked (ih tail)
      intro env owner count heap
      rw [ready env owner count heap, Result.nativeSet_bind]
  | wait poll nextStep reply before middle final value ready blocked rest ih =>
      rw [Result.wait_bind]
      exact .wait _ _ _ _ _ _ _ ready blocked (ih tail)


  | modify transition nextStep reply before middle final value ready blocked rest ih =>
      rw [nativeModify_bind]
      exact .modify _ _ _ _ _ _ _ ready blocked (ih tail)

/-- A finite ready prefix that ends at a blocked wait while excluding a peer.
Blocking retains the current shared state and is never successful completion. -/
inductive ExclusiveBlocked {γ : Type} (pid peer : PID)
    (peerPoll : Environment → Option (γ × Environment)) :
    Result α → (Nat × List (Nat × String × Term)) →
      (Nat × List (Nat × String × Term)) → Prop where
  | blocked {β : Type} (poll : Environment → Option (β × Environment)) (next : β → Result α)
      (shared : Nat × List (Nat × String × Term))
      (stopped : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = shared.1 →
        env.nativeHeap = shared.2 → poll env = none)
      (excluded : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = shared.1 →
        env.nativeHeap = shared.2 → peerPoll env = none) :
      ExclusiveBlocked pid peer peerPoll (.wait poll next) shared shared
  | wait {β : Type} (poll : Environment → Option (β × Environment))
      (next : β → Result α) (reply : β) (before after final : Nat × List (Nat × String × Term))
      (ready : ∀ env : Environment, env.currentPid = pid → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 →
        poll env = some (reply, {env with nativeRefCounter := after.1, nativeHeap := after.2}))
      (excluded : ∀ env : Environment, env.currentPid = peer → env.nativeRefCounter = before.1 →
        env.nativeHeap = before.2 → peerPoll env = none)
      (rest : ExclusiveBlocked pid peer peerPoll (next reply) after final) :
      ExclusiveBlocked pid peer peerPoll (.wait poll next) before final


end Lynx.Result
