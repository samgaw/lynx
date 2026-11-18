module
public import Positional.NamedRestart
import Lynx.Runner.CheckPost
public section
open Aeneas Aeneas.Std Lynx Lynx.NativeFile
open Positional.Concurrent (Patch Observe writer peer pins descriptors serialImage follow follow_sound)
open Positional.Nif (Payload original zeros)
open Positional.Opened (namespaceCell names)
open Positional.Properties (outcome)
open Positional.CrashPrefix (snapshot allowedImage imageWith writtenByte)
open Positional.NamedPrefix (namedState namedState_sound)
open Positional.NamedCapture (disk_captured image_shape)
open Positional.NamedRestart (filesystem cold registered reopenScript reopen named_restart_reads)
open Positional.RepeatedReopen (Interrupted every_finite_reopen)

namespace Positional.FailedSync

@[expose] def ready (persistOnError : Bool) : Environment :=
  let write := outcome "write_at" true 1 (zeros original)
  let failedSync := outcome "sync_data" false 12 ⟨#[if persistOnError then 1 else 0, 0]⟩
  let peerSync := outcome "sync_data" true 0 ByteArray.empty
  let read := outcome "read_at" true 1 (zeros original) .nil
  -- The outcome carries a live OS error capability that patch_nif consumes.
  { ({} : Environment).setPdict [(.atom "writer", writer), (.atom "peer", peer)] with
    nativeRefCounter := 12
    nativeResourceTypes := [NativeResourceArc.typeName Payload]
    nativeHeap := Positional.Concurrent.frame original (write (failedSync read)) (write (peerSync .nil)) ++
      [(12, NativeIoError.typeName, .atom "live")] }

@[expose] def withoutTear : Environment := ready false

@[expose] def program (patch : Patch) (observe : Observe) : Result Term :=
  Positional.Concurrent.patchReplies patch observe fun wrote peerReply read =>
    .tuple #[wrote, peerReply, read]

@[expose] def paired (visible durable : UInt8) (config : Concurrent.Config Term) : Bool :=
  let env := snapshot config
  let expected := pins ++ descriptors .nil .nil ++ [namespaceCell names .nil,
    (1, inodeTypeName, encode ⟨serialImage visible, serialImage durable, 0, .nil⟩)]
  (match config.outcome with
    | .ok term => term.identical (.tuple #[Term.false, Term.true, .integer visible.toNat])
    | _ => false) &&
  env.nativeRefCounter == 15 && env.nativeHeap.length == expected.length &&
    expected.all fun (expectedId, tag, value) =>
      env.nativeHeap.any fun (actualId, actualTag, actual) =>
        actualId == expectedId && actualTag == tag && actual.identical value

@[expose] def accepted (persistOnError : Bool) (config : Concurrent.Config Term) : Bool :=
  paired 7 7 config || paired 9 9 config || (!persistOnError && paired 9 7 config)

private def prefixSafe (config : Concurrent.Config Term) : Bool :=
  let env := snapshot config
  let fileSafe := match NativeFile.lookup ⟨2⟩ env, NativeFile.lookup ⟨7⟩ env with
    | some writer, some peer =>
        allowedImage writer.durable && allowedImage writer.visible &&
          (peer.script != .nil ||
            (imageWith writtenByte writer.durable && imageWith writtenByte writer.visible))
    | _, _ => false
  fileSafe && namedState 12 15 config

set_option maxHeartbeats 256000000 in
set_option maxRecDepth 8192 in
private theorem prefix_checked (persistOnError : Bool) (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant prefixSafe 64
      (.start (ready persistOnError) (program
        __PATCH__
        __OBSERVE__) elapsed) = true := by
  unfold __PATCH__
  simp only [Positional.Proofs.patch_order, monadLift_self]
  cases persistOnError <;> lynx_check_invariant

set_option maxHeartbeats 256000000 in
set_option maxRecDepth 8192 in
private theorem post_checked (persistOnError : Bool) (elapsed : PID → Nat → Nat) :
    Concurrent.checkPost (accepted persistOnError) 64
      (.start (ready persistOnError) (program
        __PATCH__
        __OBSERVE__) elapsed) = true := by
  unfold __PATCH__
  simp only [Positional.Proofs.patch_order, monadLift_self]
  cases persistOnError <;> lynx_check_post

/-- The failed writer reports false and its OS error is disposed of. The peer
reports true. The two resource pins and descriptors survive without leaked owners. -/
theorem terminal_frame (persistOnError : Bool) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term} {result : Outcome Term}
    (run : Concurrent.Run (.start (ready persistOnError)
      (program __PATCH__ __OBSERVE__) elapsed) events last)
    (terminal : Concurrent.Terminal last result) : accepted persistOnError last = true :=
  Concurrent.checkPost_sound (post_checked persistOnError elapsed) run terminal

private theorem witness {chooseLast : Concurrent.Config Term → Bool}
    {first : Concurrent.Config Term} {visible durable : UInt8}
    (found : (follow chooseLast 64 first).any (fun (_, last) => paired visible durable last)) :
    ∃ events last, Concurrent.Run first events last ∧
      Concurrent.Terminal last last.outcome ∧ paired visible durable last = true := by
  cases matched : follow chooseLast 64 first with
  | none => simp [matched] at found
  | some path =>
    obtain ⟨events, last⟩ := path
    obtain ⟨run, stopped⟩ := follow_sound matched
    exact ⟨events, last, run, .stuck stopped, by simpa [matched] using found⟩

set_option maxHeartbeats 8000000 in
/-- Even with a completed peer synchronization, a failed patch can remain
visible while the durable byte still belongs to the peer. -/
theorem visible_only_reachable (elapsed : PID → Nat → Nat) :
    ∃ events last, Concurrent.Run (.start withoutTear
      (program __PATCH__ __OBSERVE__) elapsed) events last ∧
      Concurrent.Terminal last last.outcome ∧ paired 9 7 last = true :=
  witness (chooseLast := fun _ => true) (by cbv)

private def peerFirstUntilSync (config : Concurrent.Config Term) : Bool :=
  match NativeFile.lookup ⟨7⟩ (snapshot config) with
  | some file => file.script != outcome "sync_data" true 0 ByteArray.empty .nil
  | none => true

set_option maxHeartbeats 8000000 in
/-- The peer can make the failed writer's bytes durable even when the failed
synchronization itself persists none of that write. -/
theorem peer_flushes_failed_write (elapsed : PID → Nat → Nat) :
    ∃ events last, Concurrent.Run (.start withoutTear
      (program __PATCH__ __OBSERVE__) elapsed) events last ∧
      Concurrent.Terminal last last.outcome ∧ paired 9 9 last = true :=
  witness (chooseLast := peerFirstUntilSync) (by cbv)

/-- All admitted crash images, including those at prefixes with a failed sync,
retain a reopenable inode. Once the peer syncs, no admitted image retains the
original first byte. The extracted reopen and read preserve and return the
captured byte even after any finite series of admitted interrupted reopens. -/
theorem crash_reopens (persistOnError : Bool) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term}
    (run : Concurrent.Run (.start (ready persistOnError)
      (program __PATCH__ __OBSERVE__) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot last) = some image) :
    ∃ first before,
      (first = 1 ∨ first = 7 ∨ first = 9) ∧
      image = filesystem (snapshot last).nativeRefCounter first ∧
      restartFilesystem image (reopenScript (serialImage first)) = some before ∧
      (∀ images final (_ : Interrupted first image.highWater images final),
        image.highWater ≤ final ∧ final ≤ image.highWater + 6 * images.length ∧
        (∀ next ∈ images, next = filesystem next.highWater first ∧
          restartFilesystem next (reopenScript (serialImage first)) = some (cold next.highWater first)) ∧
        ∀ (afterClock : PID → Nat → Nat) trace done result,
          Concurrent.Run (.start (registered (cold final first)) (reopen
            __OPEN__ __OBSERVE__) afterClock) trace done →
          Concurrent.Terminal done result →
          Positional.NamedRestart.accepted final first done = true) ∧
      (∀ peer, NativeFile.lookup ⟨7⟩ (snapshot last) = some peer →
        (peer.script == .nil) = true → writtenByte first = true) := by
  have checked := Concurrent.checkInvariant_sound (prefix_checked persistOnError elapsed) run
  simp only [prefixSafe, Bool.and_eq_true] at checked
  obtain ⟨table, ids, lower, _, disk, writer, found, looked, durable, visible⟩ :=
    namedState_sound checked.2
  obtain ⟨mask, bytes, persisted, captured⟩ :=
    disk_captured (snapshot last) disk table ids found chosen masks image crash
  cases other : NativeFile.lookup ⟨7⟩ (snapshot last) with
  | none => simp [looked, other] at checked
  | some peer =>
    have safe := checked.1
    simp only [looked, other, Bool.and_eq_true] at safe
    rw [durable, visible] at persisted
    have legal : allowedImage bytes = true :=
      Positional.CrashPrefix.persists_with _ _ _ mask _ safe.1.1 safe.1.2 persisted
    obtain ⟨shape, firstLegal⟩ := image_shape bytes legal
    let first := bytes[0]!
    have actual : image = filesystem (snapshot last).nativeRefCounter first := by
      rw [captured, filesystem]
      dsimp only [first]
      rw [← shape]
    have positive : 1 ≤ (snapshot last).nativeRefCounter := by omega
    refine ⟨first, cold (snapshot last).nativeRefCounter first, firstLegal, actual, ?_, ?_, ?_⟩
    · rw [actual]
      exact (named_restart_reads elapsed _ _ positive firstLegal).1
    · intro images final attempts
      have live : 1 ≤ image.highWater := by
        rw [actual]
        exact positive
      exact every_finite_reopen first firstLegal _ final live images attempts
    · intro finalPeer resolved synced
      cases Option.some.inj resolved
      have afterSync : imageWith writtenByte writer.durable = true ∧
          imageWith writtenByte writer.visible = true := by
        simpa only [bne, synced, Bool.not_true, Bool.false_or, Bool.and_eq_true] using safe.2
      have kept := Positional.CrashPrefix.persists_with _ _ _ mask _ afterSync.1 afterSync.2 persisted
      simp only [imageWith, Bool.and_eq_true, beq_iff_eq] at kept
      exact kept.1.2

end Positional.FailedSync
