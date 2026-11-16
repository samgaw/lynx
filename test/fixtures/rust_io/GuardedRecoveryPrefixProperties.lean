module
public import GuardedRecovery.AdapterProof
public import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.Interrupted
open scoped Lynx.NativeArithmetic
open GuardedRecovery.Properties GuardedRecovery.NifProperties

@[expose] def inodeFrame (heap : List (Nat × String × Term)) : Concurrent.NativeState :=
  ⟨0,heap,[],.unspecified⟩
@[expose] def expectedInode (complete : Bool) : List (Nat × String × Term) :=
  [(1,NativeFile.inodeTypeName,NativeFile.encode ⟨bytes complete,bytes complete,0,.nil⟩)]
@[expose] def stable (complete : Bool) (highWater : Nat) (env : Environment) : Bool :=
  highWater ≤ env.nativeRefCounter && env.nativeRefCounter ≤ highWater + 4 &&
  (inodeFrame (env.nativeHeap.filter (fun cell => cell.2.1 == NativeFile.inodeTypeName))).identical
    (inodeFrame (expectedInode complete)) &&
  (match NativeFile.namespaceSnapshot env with
    | none => false
    | some state => NativeFile.tablesEqual state.names names &&
      NativeFile.tablesEqual state.committed names && state.pending.isEmpty) &&
  (match NativeFile.inode 1 env with
    | none => false
    | some node => node.visible.data == (bytes complete).data &&
      node.durable.data == (bytes complete).data && node.position == 0 && node.script.identical .nil)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 32000000 in
theorem recovery_prefix_checked (complete : Bool) (highWater : Nat)
    (positive : 1 ≤ highWater) :
    Result.NativeInvariant.check (stable complete highWater) 256 AdapterProof.recovery
      (bootAt highWater complete) = true := by
  set_option cbv.maxSteps 64000000 in
  cases complete <;> cbv

theorem every_recovery_prefix (complete : Bool) (highWater : Nat)
    (positive : 1 ≤ highWater)
    (trace : Result.ReadyPrefix AdapterProof.recovery (bootAt highWater complete) residual world) :
    stable complete highWater world = true :=
  ((Result.NativeInvariant.of_check
    (recovery_prefix_checked complete highWater positive)) _ _ trace).1

/-- Native runtime prefixes retain a concrete stable image even while an IO
operation is blocked. No completed-recovery witness is inferred here. -/
theorem every_runtime_prefix (complete : Bool) (highWater : Nat)
    (positive : 1 ≤ highWater) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start (bootAt highWater complete) AdapterProof.recovery elapsed) events last) :
    ∃ world, stable complete highWater world = true ∧
      ((∃ residual, last = .start world residual elapsed) ∨
        ∃ residual, last = .running (Concurrent.State.initial world elapsed)
          [(world.currentPid,Concurrent.Task.root residual)] none false) :=
  (Result.NativeInvariant.of_check
    (recovery_prefix_checked complete highWater positive)).run elapsed run

private theorem names_equal (left right : NativeFile.Names)
    (equal : NativeFile.tablesEqual left right = true) : left = right := by
  have mapped : left.map (fun entry => (entry.1.data,entry.2)) =
      right.map (fun entry => (entry.1.data,entry.2)) := by
    simpa only [NativeFile.tablesEqual,beq_iff_eq] using equal
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons first rest ih =>
    cases right with
    | nil => simp at mapped
    | cons second tail =>
      simp only [List.map_cons,List.cons.injEq] at mapped
      have head : first = second := by
        obtain ⟨⟨a⟩,i⟩ := first
        obtain ⟨⟨b⟩,j⟩ := second
        simp only [Prod.mk.injEq] at mapped
        obtain ⟨⟨rfl,rfl⟩,tail⟩ := mapped
        rfl
      apply congrArg₂ List.cons head
      apply ih tail
      all_goals simpa only [NativeFile.tablesEqual,beq_iff_eq] using mapped.2

/-- Any permitted crash during recovery retains the same synchronized inode and
stable name. Only the freshness high-water mark changes with allocation. -/
theorem crash_during_recovery (complete : Bool) (highWater : Nat) (world : Environment)
    (preserved : stable complete highWater world = true) (choice saved : ByteArray)
    (admitted : NativeFile.persist (bytes complete) (bytes complete) choice = some saved) :
    NativeFile.filesystemCrashImage names [(1,choice)] world =
      some (imageAt world.nativeRefCounter complete) := by
  simp only [stable,Bool.and_eq_true,decide_eq_true_eq] at preserved
  obtain ⟨⟨⟨⟨lower,upper⟩,frame⟩,spaceProof⟩,node⟩ := preserved
  have frameEq := congrArg Concurrent.NativeState.heap (Concurrent.NativeState.eq_of_identical frame)
  change world.nativeHeap.filter (fun cell => cell.2.1 == NativeFile.inodeTypeName) =
    expectedInode complete at frameEq
  cases foundNamespace : NativeFile.namespaceSnapshot world with
  | none => simp [foundNamespace] at spaceProof
  | some state =>
    simp only [foundNamespace,Bool.and_eq_true] at spaceProof
    obtain ⟨⟨liveNames,committed⟩,pending⟩ := spaceProof
    have liveEq := names_equal state.names names liveNames
    have committedEq := names_equal state.committed names committed
    have pendingEq := List.isEmpty_iff.mp pending
    cases foundNode : NativeFile.inode 1 world with
    | none => simp [foundNode] at node
    | some file =>
      simp only [foundNode,Bool.and_eq_true,beq_iff_eq] at node
      obtain ⟨⟨⟨visible,durable⟩,position⟩,script⟩ := node
      have visibleEq : file.visible = bytes complete := ByteArray.ext visible
      have durableEq : file.durable = bytes complete := ByteArray.ext durable
      have scriptEq := Term.eq_of_identical script
      have same := NativeFile.persist_same (bytes complete) choice saved admitted
      subst saved
      have path : NativeFile.supportedPath fileName = true := by decide +kernel
      simp only [fileName] at path
      simp [NativeFile.filesystemCrashImage,foundNamespace,frameEq,expectedInode,
        foundNode,visibleEq,durableEq,position,scriptEq,liveEq,committedEq,pendingEq,
        NativeFile.namespaceTable,NativeFile.namespaceEntry,NativeFile.encodeNames,
        NativeFile.namespaceCrashAllowed,NativeFile.namedInode,names,fileName,path,
        List.eraseDups_cons,admitted,imageAt]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 32000000 in
/-- Retrying from any positive freshness counter uses a fresh descriptor,
returns the actual encoded words and closes the new owning mutex/file. -/
theorem retry_completes (complete : Bool) (highWater : Nat)
    (positive : 1 ≤ highWater) :
    NativeFile.restartFilesystem (imageAt highWater complete) (opening complete) =
      some (bootAt highWater complete) ∧
    Concurrent.checkPost (fun config =>
      (match config.outcome with
        | .ok value => value.identical (encodedWords complete)
        | _ => false) &&
      (Concurrent.nativeEnvironment (AdapterProof.snapshot config)).identical
        (Concurrent.nativeEnvironment {afterAt highWater complete with nativeResourceTypes := registered}))
      1024 (.start (bootAt highWater complete) AdapterProof.recovery) = true := by
  set_option cbv.maxSteps 64000000 in
  cases complete <;> constructor <;> cbv

private theorem stable_counter (complete : Bool) (highWater : Nat) (world : Environment)
    (kept : stable complete highWater world = true) :
    highWater ≤ world.nativeRefCounter ∧ world.nativeRefCounter ≤ highWater + 4 := by
  simp only [stable,Bool.and_eq_true,decide_eq_true_eq] at kept
  exact kept.1.1.1

/-- Actual recovery prefixes chained through fresh restarts. Each prefix may
stop at any native operation, independently of the other interruptions. -/
inductive InterruptedAttempts (complete : Bool) : Nat → List Environment → Nat → Prop where
  | nil (counter : Nat) : InterruptedAttempts complete counter [] counter
  | cons {counter final : Nat} {world : Environment} {worlds : List Environment}
      {residual : Result Term}
      (prefixTrace : Result.ReadyPrefix AdapterProof.recovery
        (bootAt counter complete) residual world)
      (tail : InterruptedAttempts complete world.nativeRefCounter worlds final) :
      InterruptedAttempts complete counter (world :: worlds) final

/-- Interrupting before the first IO operation is admitted at every finite
retry count, so the repeated-recovery relation is inhabited independently of fuel. -/
theorem interrupt_before_io (complete : Bool) (counter count : Nat) :
    InterruptedAttempts complete counter (List.replicate count (bootAt counter complete)) counter := by
  induction count with
  | zero => exact .nil _
  | succ count ih =>
    simpa only [List.replicate_succ] using InterruptedAttempts.cons (Result.ReadyPrefix.refl _ _) ih

/-- Every admitted persistence choice at an interrupted recovery produces the
same synchronized bytes and stable name, with fresh volatile state on restart. -/
@[expose] def crashSafe (complete : Bool) (world : Environment) : Prop :=
  ∀ choice saved, NativeFile.persist (bytes complete) (bytes complete) choice = some saved →
    NativeFile.filesystemCrashImage names [(1,choice)] world =
      some (imageAt world.nativeRefCounter complete) ∧
    NativeFile.restartFilesystem (imageAt world.nativeRefCounter complete) (opening complete) =
      some (bootAt world.nativeRefCounter complete)

theorem interrupted_attempts_safe (complete : Bool) (counter final : Nat)
    (worlds : List Environment) (positive : 1 ≤ counter)
    (attempts : InterruptedAttempts complete counter worlds final) :
    counter ≤ final ∧ final ≤ counter + 4 * worlds.length ∧
      ∀ world ∈ worlds, crashSafe complete world := by
  induction attempts with
  | nil => simp
  | @cons counter final world worlds residual head tail ih =>
    have kept := every_recovery_prefix complete counter positive head
    obtain ⟨lower,upper⟩ := stable_counter complete counter world kept
    obtain ⟨tailLower,tailUpper,tailSafe⟩ := ih (by omega)
    refine ⟨by omega, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro candidate member
      rcases List.mem_cons.mp member with equal | member
      · subst candidate
        intro choice saved admitted
        exact ⟨crash_during_recovery complete counter world kept choice saved admitted,
          (retry_completes complete world.nativeRefCounter (by omega)).1⟩
      · exact tailSafe candidate member

/-- Any finite number of interrupted actual adapter executions preserves every
admitted crash image. The final fresh recovery completes and closes its owners.
The number of interruptions and the initial freshness counter have no fixed bound;
the declared ready IO scripts and stable namespace remain explicit preconditions. -/
theorem every_finite_retry (complete : Bool) (counter final : Nat)
    (worlds : List Environment) (positive : 1 ≤ counter)
    (attempts : InterruptedAttempts complete counter worlds final) :
    (∀ world ∈ worlds, crashSafe complete world) ∧
    Concurrent.checkPost (fun config =>
      (match config.outcome with
        | .ok value => value.identical (encodedWords complete)
        | _ => false) &&
      (Concurrent.nativeEnvironment (AdapterProof.snapshot config)).identical
        (Concurrent.nativeEnvironment {afterAt final complete with nativeResourceTypes := registered}))
      1024 (.start (bootAt final complete) AdapterProof.recovery) = true := by
  obtain ⟨lower,_,safe⟩ := interrupted_attempts_safe complete counter final worlds positive attempts
  exact ⟨safe,(retry_completes complete final (by omega)).2⟩

end GuardedRecovery.Interrupted

#check GuardedRecovery.Interrupted.every_finite_retry
