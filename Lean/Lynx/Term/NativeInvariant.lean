module

public import Lynx.Term.NativeTrace

public section
namespace Lynx.Result

/-- Every finite ready prefix retains the environment predicate and stays in the
local/native fragment. Blocking and verification exhaustion are not successful
completion. The predicate observes every intermediate state, not only returns. -/
@[expose] def NativeInvariant (holds : Environment → Prop) (computation : Result α)
    (before : Environment) : Prop :=
  ∀ residual after, ReadyPrefix computation before residual after → holds after ∧
    match residual with
    | .schedule .. | .send .. | .receive .. | .request .. => False
    | _ => True

private def BindPrefix (computation : Result α) (before : Environment)
    (next : α → Result β) (residual : Result β) (after : Environment) : Prop :=
  (∃ middle, ReadyPrefix computation before middle after ∧ residual = middle >>= next) ∨
  ∃ value midway, ReadyPrefix computation before (.ok value) midway ∧
    ReadyPrefix (next value) midway residual after

private theorem BindPrefix.prepend {computation middle : Result α} {before midway : Environment}
    {next : α → Result β} {residual : Result β} {after : Environment}
    (headTrace : ReadyPrefix computation before middle midway)
    (split : BindPrefix middle midway next residual after) :
    BindPrefix computation before next residual after := by
  rcases split with ⟨rest, trace, equal⟩ | ⟨value, env, trace, tail⟩
  · exact .inl ⟨rest, headTrace.trans trace, equal⟩
  · exact .inr ⟨value, env, headTrace.trans trace, tail⟩

private theorem bind_prefix (computation : Result α) (next : α → Result β)
    (before after : Environment) (residual : Result β)
    (trace : ReadyPrefix (computation >>= next) before residual after) :
    BindPrefix computation before next residual after := by
  induction computation generalizing before after residual with
  | ok value => exact .inr ⟨value, before, .refl _ _, trace⟩
  | error exception => cases trace; exact .inl ⟨_, .refl _ _, rfl⟩
  | get body ih =>
      rw [get_bind] at trace
      cases trace with
      | refl => exact .inl ⟨_, .refl _ _, rfl⟩
      | get _ _ _ _ rest =>
          exact (ih _ _ _ _ _ rest).prepend (.get _ _ _ _ (.refl _ _))
  | nativeGet body ih =>
      rw [nativeGet_bind] at trace
      cases trace with
      | refl => exact .inl ⟨_, .refl _ _, rfl⟩
      | nativeGet _ _ _ _ rest =>
          exact (ih _ _ _ _ _ rest).prepend (.nativeGet _ _ _ _ (.refl _ _))
  | set updated body ih =>
      rw [set_bind] at trace
      cases trace with
      | refl => exact .inl ⟨_, .refl _ _, rfl⟩
      | set _ _ _ _ _ rest =>
          exact (ih _ _ _ _ rest).prepend (.set _ _ _ _ _ (.refl _ _))
  | nativeSet updated body ih =>
      rw [nativeSet_bind] at trace
      cases trace with
      | refl => exact .inl ⟨_, .refl _ _, rfl⟩
      | nativeSet _ _ _ _ _ rest =>
          exact (ih _ _ _ _ rest).prepend (.nativeSet _ _ _ _ _ (.refl _ _))
  | nativeModify transition body ih =>
      rw [nativeModify_bind] at trace
      cases trace with
      | refl => exact .inl ⟨_, .refl _ _, rfl⟩
      | nativeModify _ _ reply _ updated _ _ ready rest =>
          exact (ih _ _ _ _ _ rest).prepend (.nativeModify _ _ reply _ updated _ _ ready (.refl _ _))
  | wait poll body ih =>
      rw [wait_bind] at trace
      cases trace with
      | refl => exact .inl ⟨_, .refl _ _, rfl⟩
      | wait _ _ reply _ updated _ _ ready rest =>
          exact (ih _ _ _ _ _ rest).prepend (.wait _ _ reply _ updated _ _ ready (.refl _ _))
  | schedule options child body _ _ =>
      rw [schedule_bind] at trace
      cases trace
      exact .inl ⟨_, .refl _ _, rfl⟩
  | send pid message body _ =>
      rw [send_bind] at trace
      cases trace
      exact .inl ⟨_, .refl _ _, rfl⟩
  | receive timeout select body _ =>
      rw [receive_bind] at trace
      cases trace
      exact .inl ⟨_, .refl _ _, rfl⟩
  | request query body _ =>
      rw [request_bind] at trace
      cases trace
      exact .inl ⟨_, .refl _ _, rfl⟩


/-- A successful bound computation actually completes its callee before entering
the continuation. Both prefixes retain their concrete intermediate environment. -/
theorem ReadyPrefix.bind_returns {computation : Result α} {next : α → Result β}
    {before after : Environment} {value : β}
    (trace : ReadyPrefix (computation >>= next) before (.ok value) after) :
    ∃ returned middle, ReadyPrefix computation before (.ok returned) middle ∧
      ReadyPrefix (next returned) middle (.ok value) after := by
  have split := bind_prefix computation next before after (.ok value) trace
  rcases split with ⟨residual, headTrace, equal⟩ | ⟨returned, middle, headTrace, rest⟩
  · cases residual
    all_goals first
      | exact ⟨_, after, headTrace, equal ▸ ReadyPrefix.refl _ _⟩
      | contradiction
  · exact ⟨returned, middle, headTrace, rest⟩

namespace NativeInvariant

theorem initial {holds : Environment → Prop} {computation : Result α} {before : Environment}
    (safe : NativeInvariant holds computation before) : holds before :=
  (safe _ _ (.refl _ _)).1

theorem bind {holds : Environment → Prop} {computation : Result α} {before : Environment}
    (safe : NativeInvariant holds computation before) (next : α → Result β)
    (continuation : ∀ value midway, ReadyPrefix computation before (.ok value) midway →
      NativeInvariant holds (next value) midway) :
    NativeInvariant holds (computation >>= next) before := by
  intro residual after trace
  have split := bind_prefix computation next before after residual trace
  rcases split with ⟨middle, headTrace, rfl⟩ | ⟨value, midway, headTrace, rest⟩
  · have kept := safe _ _ headTrace
    cases middle with
    | ok value => exact continuation value after headTrace _ _ (.refl _ _)
    | error | get | set | nativeGet | nativeSet | nativeModify | wait => exact ⟨kept.1, trivial⟩
    | schedule | send | receive | request => exact False.elim kept.2
  · exact continuation value midway headTrace _ _ rest


theorem after_prefix {holds : Environment → Prop} {computation residual : Result α}
    {before after : Environment} (safe : NativeInvariant holds computation before)
    (headTrace : ReadyPrefix computation before residual after) :
    NativeInvariant holds residual after := by
  intro rest final tail
  exact safe _ _ (headTrace.trans tail)

theorem ok (holds : Environment → Prop) (value : α) (before : Environment)
    (valid : holds before) : NativeInvariant holds (.ok value) before := by
  intro residual after trace
  cases trace
  exact ⟨valid, trivial⟩

theorem error (holds : Environment → Prop) (exception : Exception) (before : Environment)
    (valid : holds before) : NativeInvariant holds (.error exception : Result α) before := by
  intro residual after trace
  cases trace
  exact ⟨valid, trivial⟩

theorem get {holds : Environment → Prop} (next : Environment → Result α) (before : Environment)
    (safe : NativeInvariant holds (next before) before) :
    NativeInvariant holds (.get next) before := by
  intro residual after trace
  cases trace with
  | refl => exact ⟨safe.initial, trivial⟩
  | get _ _ _ _ rest => exact safe _ _ rest

theorem nativeGet {holds : Environment → Prop} (next : Environment → Result α) (before : Environment)
    (safe : NativeInvariant holds (next before) before) :
    NativeInvariant holds (.nativeGet next) before := by
  intro residual after trace
  cases trace with
  | refl => exact ⟨safe.initial, trivial⟩
  | nativeGet _ _ _ _ rest => exact safe _ _ rest

theorem set {holds : Environment → Prop} (updated : Environment) (next : Result α) (before : Environment)
    (valid : holds before) (safe : NativeInvariant holds next updated) :
    NativeInvariant holds (.set updated next) before := by
  intro residual after trace
  cases trace with
  | refl => exact ⟨valid, trivial⟩
  | set _ _ _ _ _ rest => exact safe _ _ rest

theorem nativeSet {holds : Environment → Prop} (updated : Environment) (next : Result α)
    (before : Environment) (valid : holds before) (safe : NativeInvariant holds next updated) :
    NativeInvariant holds (.nativeSet updated next) before := by
  intro residual after trace
  cases trace with
  | refl => exact ⟨valid, trivial⟩
  | nativeSet _ _ _ _ _ rest => exact safe _ _ rest

theorem nativeModify {holds : Environment → Prop} (transition : Environment → β × Environment)
    (next : β → Result α) (before : Environment) (valid : holds before)
    (safe : NativeInvariant holds (next (transition before).1) (transition before).2) :
    NativeInvariant holds (.nativeModify transition next) before := by
  intro residual after trace
  cases trace with
  | refl => exact ⟨valid, trivial⟩
  | nativeModify _ _ reply _ updated _ _ ready rest =>
      have selected : NativeInvariant holds (next reply) updated := by
        simpa only [ready] using safe
      exact selected _ _ rest

theorem wait {holds : Environment → Prop} (poll : Environment → Option (β × Environment))
    (next : β → Result α) (before : Environment) (valid : holds before)
    (safe : ∀ reply updated, poll before = some (reply, updated) →
      NativeInvariant holds (next reply) updated) :
    NativeInvariant holds (.wait poll next) before := by
  intro residual after trace
  cases trace with
  | refl => exact ⟨valid, trivial⟩
  | wait _ _ reply _ updated _ _ ready rest => exact safe _ _ ready _ _ rest

private theorem blocked_stuck {poll : Environment → Option (β × Environment)}
    (next : β → Result α) (env : Environment) (elapsed : PID → Nat → Nat)
    (blocked : poll env = none) :
    (Concurrent.Config.running (Concurrent.State.initial env elapsed)
      [(env.currentPid, Concurrent.Task.root (.wait poll next))] none false).successors = [] := by
  simp [Concurrent.Config.successors, Concurrent.splits, Concurrent.Task.transitions,
    Concurrent.Task.own, Concurrent.Task.root, blocked, Concurrent.Task.deliveries,
    Concurrent.deliverable, Concurrent.deliverableFrom, Concurrent.State.initial,
    Concurrent.State.firing, Concurrent.firstOfEach, Concurrent.Kernel.map_eq,
    Concurrent.State.nativeView, Concurrent.State.view, Concurrent.State.process]

/-- A native invariant covers every raw runtime prefix. A blocked wait can enter
an initial scheduler state but, with no peers or timers, cannot change the native
snapshot while blocked. This asserts neither completion nor concurrent safety. -/
theorem run {holds : Environment → Prop} {computation : Result α} {before : Environment}
    (safe : NativeInvariant holds computation before) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config α}
    (executed : Concurrent.Run (.start before computation elapsed) events last) :
    ∃ env, holds env ∧
      ((∃ residual, last = .start env residual elapsed) ∨
        ∃ residual, last = .running (Concurrent.State.initial env elapsed)
          [(env.currentPid, Concurrent.Task.root residual)] none false) := by
  induction events generalizing before computation last with
  | nil => cases executed; exact ⟨before, safe.initial, .inl ⟨_, rfl⟩⟩
  | cons event events ih =>
      cases executed with
      | step moved rest =>
          cases computation with
          | get next | nativeGet next =>
              simp only [Concurrent.Step, Concurrent.Config.successors, List.mem_singleton,
                Prod.mk.injEq] at moved
              obtain ⟨rfl, rfl⟩ := moved
              apply ih (safe.after_prefix ?_) rest
              first | exact .get _ _ _ _ (.refl _ _) | exact .nativeGet _ _ _ _ (.refl _ _)
          | set updated next | nativeSet updated next =>
              simp only [Concurrent.Step, Concurrent.Config.successors, List.mem_singleton,
                Prod.mk.injEq] at moved
              obtain ⟨rfl, rfl⟩ := moved
              apply ih (safe.after_prefix ?_) rest
              first | exact .set _ _ _ _ _ (.refl _ _) | exact .nativeSet _ _ _ _ _ (.refl _ _)
          | nativeModify transition next =>
              simp only [Concurrent.Step, Concurrent.Config.successors, List.mem_singleton,
                Prod.mk.injEq] at moved
              obtain ⟨rfl, rfl⟩ := moved
              apply ih (safe.after_prefix (.nativeModify _ _ _ _ _ _ _ rfl (.refl _ _))) rest
          | wait poll next =>
              cases ready : poll before with
              | none =>
                  simp only [Concurrent.Step, Concurrent.Config.successors, ready, List.mem_singleton,
                    Prod.mk.injEq] at moved
                  obtain ⟨rfl, rfl⟩ := moved
                  cases rest with
                  | refl => exact ⟨before, safe.initial, .inr ⟨_, rfl⟩⟩
                  | step moved _ =>
                      have stuck := blocked_stuck next before elapsed ready
                      simp only [Concurrent.Step, stuck, List.not_mem_nil] at moved
              | some reply =>
                  obtain ⟨value, updated⟩ := reply
                  simp only [Concurrent.Step, Concurrent.Config.successors, ready, List.mem_singleton,
                    Prod.mk.injEq] at moved
                  obtain ⟨rfl, rfl⟩ := moved
                  exact ih (safe.after_prefix (.wait _ _ _ _ _ _ _ ready (.refl _ _))) rest
          | ok | error => simp [Concurrent.Step, Concurrent.Config.successors, Concurrent.isRequest] at moved
          | schedule | send | receive | request => exact False.elim (safe _ _ (.refl _ _)).2


end NativeInvariant
end Lynx.Result
