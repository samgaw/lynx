module
public import GuardedRecovery.AdapterProof
public import Mathlib.Tactic.IntervalCases
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace GuardedRecovery.Interrupted
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
    (lower : 12 ≤ highWater) (upper : highWater ≤ 16) :
    Result.NativeInvariant.check (stable complete highWater) 256 AdapterProof.recovery
      (bootAt highWater complete) = true := by
  set_option cbv.maxSteps 64000000 in
  interval_cases highWater <;> cases complete <;> cbv

theorem every_recovery_prefix (complete : Bool) (highWater : Nat)
    (lower : 12 ≤ highWater) (upper : highWater ≤ 16)
    (trace : Result.ReadyPrefix AdapterProof.recovery (bootAt highWater complete) residual world) :
    stable complete highWater world = true :=
  ((Result.NativeInvariant.of_check
    (recovery_prefix_checked complete highWater lower upper)) _ _ trace).1

/-- Native runtime prefixes retain a concrete stable image even while an IO
operation is blocked. No completed-recovery witness is inferred here. -/
theorem every_runtime_prefix (complete : Bool) (highWater : Nat)
    (lower : 12 ≤ highWater) (upper : highWater ≤ 16) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start (bootAt highWater complete) AdapterProof.recovery elapsed) events last) :
    ∃ world, stable complete highWater world = true ∧
      ((∃ residual, last = .start world residual elapsed) ∨
        ∃ residual, last = .running (Concurrent.State.initial world elapsed)
          [(world.currentPid,Concurrent.Task.root residual)] none false) :=
  (Result.NativeInvariant.of_check
    (recovery_prefix_checked complete highWater lower upper)).run elapsed run

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
/-- Retrying from any first-recovery allocation prefix uses a fresh descriptor,
returns the actual encoded words and closes the new owning mutex/file. -/
theorem retry_completes (complete : Bool) (highWater : Nat)
    (lower : 12 ≤ highWater) (upper : highWater ≤ 20) :
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
  interval_cases highWater <;> cases complete <;> constructor <;> cbv

private theorem stable_counter (complete : Bool) (highWater : Nat) (world : Environment)
    (kept : stable complete highWater world = true) :
    highWater ≤ world.nativeRefCounter ∧ world.nativeRefCounter ≤ highWater + 4 := by
  simp only [stable,Bool.and_eq_true,decide_eq_true_eq] at kept
  exact kept.1.1.1

/-- Two crashes may interrupt either recovery at any modelled native prefix.
Each restart discards old owners, and the final fresh retry completes with the
same decoded data. This is bounded repetition, not an unbounded retry claim. -/
theorem two_interrupted_recoveries (complete : Bool)
    (first : Result.ReadyPrefix AdapterProof.recovery (bootAt 12 complete) residual1 world1)
    (second : Result.ReadyPrefix AdapterProof.recovery
      (bootAt world1.nativeRefCounter complete) residual2 world2)
    (choice1 saved1 choice2 saved2 : ByteArray)
    (admitted1 : NativeFile.persist (bytes complete) (bytes complete) choice1 = some saved1)
    (admitted2 : NativeFile.persist (bytes complete) (bytes complete) choice2 = some saved2) :
    NativeFile.filesystemCrashImage names [(1,choice1)] world1 =
      some (imageAt world1.nativeRefCounter complete) ∧
    NativeFile.restartFilesystem (imageAt world1.nativeRefCounter complete) (opening complete) =
      some (bootAt world1.nativeRefCounter complete) ∧
    NativeFile.filesystemCrashImage names [(1,choice2)] world2 =
      some (imageAt world2.nativeRefCounter complete) ∧
    NativeFile.restartFilesystem (imageAt world2.nativeRefCounter complete) (opening complete) =
      some (bootAt world2.nativeRefCounter complete) ∧
    Concurrent.checkPost (fun config =>
      (match config.outcome with
        | .ok value => value.identical (encodedWords complete)
        | _ => false) &&
      (Concurrent.nativeEnvironment (AdapterProof.snapshot config)).identical
        (Concurrent.nativeEnvironment {afterAt world2.nativeRefCounter complete with
          nativeResourceTypes := registered})) 1024
      (.start (bootAt world2.nativeRefCounter complete) AdapterProof.recovery) = true := by
  have kept1 := every_recovery_prefix complete 12 (by decide) (by decide) first
  obtain ⟨lower1,upper1⟩ := stable_counter complete 12 world1 kept1
  have kept2 := every_recovery_prefix complete world1.nativeRefCounter lower1 (by omega) second
  obtain ⟨lower2,upper2⟩ := stable_counter complete world1.nativeRefCounter world2 kept2
  exact ⟨crash_during_recovery complete 12 world1 kept1 choice1 saved1 admitted1,
    (retry_completes complete world1.nativeRefCounter lower1 (by omega)).1,
    crash_during_recovery complete world1.nativeRefCounter world2 kept2 choice2 saved2 admitted2,
    retry_completes complete world2.nativeRefCounter (by omega) (by omega)⟩

end GuardedRecovery.Interrupted

#check GuardedRecovery.Interrupted.two_interrupted_recoveries
