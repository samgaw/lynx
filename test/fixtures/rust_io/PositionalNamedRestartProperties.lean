module
public import Positional.Crash
public import Lynx.Concurrent
import Lynx.Runner.CheckPost
import Lynx.Runner.NativeArithmetic
public section
open Aeneas Aeneas.Std Lynx Lynx.NativeFile

namespace Positional.NamedRestart
open scoped Lynx.NativeArithmetic
open Positional.Nif (Payload zeros)
open Positional.Opened (fileName names inodeCell namespaceCell openCall)
open Positional.Concurrent (Observe serialImage)

@[expose] def reopenScript (contents : ByteArray) : Term :=
  Positional.Opened.openChoice true 0
    (Positional.Properties.outcome "read_at" true 1 (zeros contents) .nil) .nil

@[expose] def filesystem (counter : Nat) (first : UInt8) : FilesystemImage :=
  ⟨names, [(1, serialImage first)], counter⟩

@[expose] def cold (counter : Nat) (first : UInt8) : Environment :=
  { nativeRefCounter := counter
    nativeHeap := [namespaceCell names (reopenScript (serialImage first)), inodeCell (serialImage first)] }

@[expose] def registered (env : Environment) : Environment :=
  {env with nativeResourceTypes := [NativeResourceArc.typeName Payload]}

@[expose] def afterSeven : Environment := registered (cold 14 7)

@[expose] def reopen (opener : Positional.Opened.Opener) (observe : Observe) : Result Term := do
  let resource ← openCall opener
  let owner ← NativeResourceArc.decode resource
  let byte ← Rustler.executeNative (observe owner 0#u64) (Rustler.encodeOption Rustler.encodeUnsigned)
  Result.ok (.tuple #[resource, byte])

@[expose] def accepted (counter : Nat) (first : UInt8) (config : Concurrent.Config Term) : Bool :=
  let env := match config with
    | .start initial .. => initial
    | .running state .. => state.nativeView []
  let expected := NativeResourceArc.vmCells (⟨⟨counter + 1⟩⟩ : Payload)
      (counter + 2) (counter + 4) (counter + 5) ++
    [(counter + 1, writableHandleTypeName, encodeHandle ⟨1, 0, .nil⟩),
     namespaceCell names .nil, inodeCell (serialImage first)]
  (match config.outcome with
    | .ok term =>
        let value := Term.tuple #[.nativeReference (counter + 5), .integer first.toNat]
        Term.compareExact (Term.fuel term value) term value == .eq
    | _ => false) &&
  env.nativeRefCounter == counter + 6 && env.nativeHeap.length == expected.length &&
    expected.all fun (expectedId, tag, value) =>
      env.nativeHeap.any fun (actualId, actualTag, actual) =>
        actualId == expectedId && actualTag == tag &&
          Term.compareExact (Term.fuel actual value) actual value == .eq

set_option maxHeartbeats 16000000 in
set_option maxRecDepth 8192 in
theorem named_restart_reads (elapsed : PID → Nat → Nat) (counter : Nat) (first : UInt8)
    (positive : 1 ≤ counter) (byte : first = 1 ∨ first = 7 ∨ first = 9) :
    restartFilesystem (filesystem counter first) (reopenScript (serialImage first)) =
        some (cold counter first) ∧
    Concurrent.checkPost (accepted counter first) 64
      (.start (registered (cold counter first)) (reopen
        __OPEN__
        __OBSERVE__) elapsed) = true := by
  rcases byte with rfl | rfl | rfl <;> constructor <;> cbv

end Positional.NamedRestart

namespace Positional.NamedCapture
open Positional.Opened (names fileName)
open Positional.Concurrent (ready program serialImage)
open Positional.CrashPrefix (snapshot allowedImage imageWith writtenByte synchronized)
open Positional.NamedPrefix (checkpoint nodeIds retains_named_inode)
open Positional.NamedRestart (filesystem cold registered reopenScript reopen accepted named_restart_reads)

private theorem table_unique (chosen selected : Names)
    (table : namespaceTable (encodeNames chosen) = some selected) :
    (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length := by
  simp only [encodeNames,namespaceTable] at table
  split at table
  · contradiction
  · simp only [Bind.bind,Option.bind_eq_some_iff] at table
    rcases table with ⟨mapped,parsed,table⟩
    split at table
    · contradiction
    · rename_i unique
      cases table
      simpa using unique

private theorem names_fixed (selected : Names)
    (unique : (selected.map (fun entry => entry.1.data)).eraseDups.length = selected.length)
    (allowed : namespaceCrashAllowed checkpoint selected = true) : selected = names := by
  simp [namespaceCrashAllowed,checkpoint,names,namedInode] at allowed
  have mapped : selected.map (fun entry => entry.1.data) =
      List.replicate selected.length fileName.data := by
    apply List.map_eq_replicate_iff.mpr
    intro entry member
    exact (allowed.1 entry.1 entry.2 member).symm
  rw [mapped] at unique
  rcases allowed.2 with ⟨actual,found⟩
  cases selected with
  | nil => simp at found
  | cons head tail =>
    have empty : tail = [] := by
      have length : tail.length = 0 := by
        simpa [List.replicate_succ,List.eraseDups_cons] using unique.symm
      exact List.eq_nil_of_length_eq_zero length
    subst tail
    have same : head.1 = fileName :=
      ByteArray.ext (allowed.1 head.1 head.2 (by simp)).symm
    obtain ⟨path, node⟩ := head
    simp only at same
    subst path
    simp at found
    simp [names,found]

private theorem one_node {α : Type} (items : List α) (identity : α → Nat)
    (ids : items.map identity = [1]) : ∃ node, items = [node] ∧ identity node = 1 := by
  cases items with
  | nil => simp at ids
  | cons node rest =>
    simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at ids
    exact ⟨node, by simp [ids.2], ids.1⟩

theorem disk_captured (env : Environment) (disk : NativeFile.State) {script : Term}
    (tables : namespaceSnapshot env = some { checkpoint with script := script })
    (ids : nodeIds env = [1]) (found : inode 1 env = some disk)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (admitted : filesystemCrashImage chosen masks env = some image) :
    ∃ mask bytes, persist disk.durable disk.visible mask = some bytes ∧
      image = ⟨names, [(1, bytes)], env.nativeRefCounter⟩ := by
  unfold nodeIds at ids
  obtain ⟨node, nodes, nodeId⟩ := one_node _ _ ids
  unfold filesystemCrashImage at admitted
  rw [tables] at admitted
  simp only [Bind.bind, Option.bind_some, Option.bind_eq_some_iff] at admitted
  rcases admitted with ⟨selected, normalized, admitted⟩
  split at admitted
  · contradiction
  · rename_i allowed
    have permit : namespaceCrashAllowed { checkpoint with script := script } selected = true := by
      simpa using allowed
    have selectedNames := names_fixed selected (table_unique chosen selected normalized) permit
    rw [nodes] at admitted
    split at admitted
    · contradiction
    · rename_i aligned
      have maskIds : masks.map Prod.fst = [1] := by
        simpa [nodeId] using aligned
      obtain ⟨entry, rfl, entryId⟩ := one_node masks Prod.fst maskIds
      obtain ⟨number,mask⟩ := entry
      change number = 1 at entryId
      subst number
      rw [selectedNames] at admitted
      change node.1 = 1 at nodeId
      simp [List.mapM, List.mapM.loop, nodeId, found] at admitted
      cases choice : persist disk.durable disk.visible mask with
      | none => simp [choice] at admitted
      | some bytes =>
        simp [choice, names] at admitted
        exact ⟨mask, bytes, by simp [choice], admitted.symm⟩

theorem image_shape (bytes : ByteArray) (valid : allowedImage bytes = true) :
    bytes = serialImage bytes[0]! ∧ (bytes[0]! = 1 ∨ bytes[0]! = 7 ∨ bytes[0]! = 9) := by
  simp only [allowedImage, imageWith, writtenByte, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at valid
  refine ⟨?_, valid.1.2⟩
  apply ByteArray.ext
  apply _root_.Array.ext
  · simpa [serialImage, ← ByteArray.size_data] using valid.1.1
  · intro i inside expected
    have atMost : i = 0 ∨ i = 1 := by
      have hb : i < 2 := by simpa [serialImage] using expected
      omega
    rcases atMost with rfl | rfl
    · simp [serialImage, getElem!_pos bytes 0 (by omega : 0 < bytes.size)]; rfl
    · simp [serialImage]
      rw [getElem!_pos bytes 1 (by omega : 1 < bytes.size)] at valid
      exact valid.2

/-- Every filesystem image admitted at a reachable prefix restarts with only
the captured named image. The extracted Rustler opener reopens that inode, and
the extracted observer returns its exact first byte through a fresh resource. -/
theorem named_crash_reopens (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term}
    (run : Concurrent.Run (.start ready (program
      __PATCH__
      __OBSERVE__) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot last) = some image) :
    ∃ first before,
      (first = 1 ∨ first = 7 ∨ first = 9) ∧
      image = filesystem (snapshot last).nativeRefCounter first ∧
      restartFilesystem image (reopenScript (serialImage first)) = some before ∧
      (∀ (afterClock : PID → Nat → Nat) trace final result,
        Concurrent.Run (.start (registered before) (reopen
          __OPEN__
          __OBSERVE__) afterClock) trace final →
        Concurrent.Terminal final result → accepted image.highWater first final = true) ∧
      (∀ writer peer, NativeFile.lookup ⟨2⟩ (snapshot last) = some writer →
        NativeFile.lookup ⟨7⟩ (snapshot last) = some peer →
        synchronized writer peer = true → writtenByte first = true) := by
  obtain ⟨table, ids, lower, _, disk, writer, found, looked, durable, visible⟩ :=
    retains_named_inode elapsed run
  obtain ⟨mask, bytes, persisted, captured⟩ :=
    disk_captured (snapshot last) disk table ids found chosen masks image crash
  have fileCapture : crashImage ⟨2⟩ mask (snapshot last) =
      some ⟨bytes, (snapshot last).nativeRefCounter⟩ := by
    simp [crashImage, looked, ← durable, ← visible, persisted]
  obtain ⟨legal, synced⟩ :=
    Positional.CrashPrefix.crashes_preserve_positional_bytes elapsed events last run mask _ fileCapture
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
  · intro afterClock trace final result next terminal
    rw [actual]
    exact Concurrent.checkPost_sound (named_restart_reads afterClock _ _ positive firstLegal).2 next terminal
  · intro front back firstLookup secondLookup afterSync
    have safe := synced front back firstLookup secondLookup afterSync
    simp only [imageWith, Bool.and_eq_true] at safe
    exact safe.1.2

end Positional.NamedCapture

namespace Positional.Reopening
open scoped Lynx.NativeArithmetic
open Positional.CrashPrefix (snapshot)
open Positional.Concurrent (serialImage)
open Positional.NamedPrefix (nodeIds singleName)
open Positional.NamedRestart (cold registered reopen)

@[expose] def stable (counter : Nat) (first : UInt8) (cfg : Concurrent.Config Term) : Bool :=
  let env := snapshot cfg
  (counter ≤ env.nativeRefCounter && env.nativeRefCounter ≤ counter + 6) &&
  nodeIds env == [1] &&
  (match namespaceSnapshot env with
    | none => false
    | some table => singleName table.names && singleName table.committed &&
        table.pending.isEmpty) &&
  (match inode 1 env with
    | none => false
    | some disk => disk.durable.data == (serialImage first).data &&
        disk.visible.data == (serialImage first).data)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
theorem reopen_prefix_checked (counter : Nat) (first : UInt8) (positive : 1 ≤ counter)
    (byte : first = 1 ∨ first = 7 ∨ first = 9) (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant (stable counter first) 64
      (.start (registered (cold counter first)) (reopen
        __OPEN__
        __OBSERVE__) elapsed) = true := by
  set_option cbv.maxSteps 64000000 in
  rcases byte with rfl | rfl | rfl <;> cbv

end Positional.Reopening

namespace Positional.RepeatedReopen
open scoped Lynx.NativeArithmetic
open Positional.Opened (names)
open Positional.Concurrent (serialImage)
open Positional.CrashPrefix (snapshot)
open Positional.NamedPrefix (checkpoint)
open Positional.NamedRestart (filesystem cold registered reopenScript reopen accepted named_restart_reads)
open Positional.Reopening (stable reopen_prefix_checked)

/-- A crash at any prefix of an actual reopen/read preserves the stable named
image and can advance the high-water mark by at most six allocations. -/
theorem crash_during_reopen (counter : Nat) (first : UInt8) (positive : 1 ≤ counter)
    (byte : first = 1 ∨ first = 7 ∨ first = 9) (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term}
    (run : Concurrent.Run (.start (registered (cold counter first))
      (reopen
        __OPEN__
        __OBSERVE__) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (snapshot last) = some image) :
    image = filesystem (snapshot last).nativeRefCounter first ∧
      counter ≤ image.highWater ∧ image.highWater ≤ counter + 6 := by
  have stableRun := Concurrent.checkInvariant_sound
    (reopen_prefix_checked counter first positive byte elapsed) run
  simp only [stable, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at stableRun
  obtain ⟨⟨⟨bounds, ids⟩, tableOK⟩, diskOK⟩ := stableRun
  cases tables : namespaceSnapshot (snapshot last) with
  | none => simp [tables] at tableOK
  | some table =>
    cases found : inode 1 (snapshot last) with
    | none => simp [found] at diskOK
    | some disk =>
      simp only [tables, Bool.and_eq_true, List.isEmpty_iff] at tableOK
      simp only [found, Bool.and_eq_true, beq_iff_eq] at diskOK
      obtain ⟨⟨visible, durable⟩, pending⟩ := tableOK
      have retained : table = { checkpoint with script := table.script } := by
        rcases table with ⟨visibleNames, durableNames, pendingNames, script⟩
        dsimp only at visible durable pending ⊢
        rw [Positional.NamedPrefix.single_eq visible, Positional.NamedPrefix.single_eq durable, pending]
        rfl
      rw [retained] at tables
      obtain ⟨mask, data, persisted, captured⟩ :=
        Positional.NamedCapture.disk_captured (snapshot last) disk tables ids found chosen masks image crash
      have dataEq : data = serialImage first := by
        rw [ByteArray.ext diskOK.1, ByteArray.ext diskOK.2] at persisted
        exact persist_same _ _ _ persisted
      subst data
      exact ⟨captured, by rw [captured]; exact bounds.1, by rw [captured]; exact bounds.2⟩

/-- Each interruption records a disk image admitted at an actual Rustler
reopen/read prefix. The next attempt starts with fresh runtime state. -/
inductive Interrupted (first : UInt8) : Nat → List FilesystemImage → Nat → Prop where
  | done (counter : Nat) : Interrupted first counter [] counter
  | crash {counter final : Nat} {elapsed : PID → Nat → Nat} {events : List Concurrent.Event}
      {last : Concurrent.Config Term} {chosen : Names} {masks : List (Nat × ByteArray)}
      {image : FilesystemImage} {images : List FilesystemImage}
      (run : Concurrent.Run (.start (registered (cold counter first)) (reopen
        __OPEN__
        __OBSERVE__) elapsed)
        events last)
      (saved : filesystemCrashImage chosen masks (snapshot last) = some image)
      (next : Interrupted first image.highWater images final) :
      Interrupted first counter (image :: images) final

set_option maxRecDepth 8192 in
/-- Every retry count is admitted by crashing before the first I/O step. -/
theorem interrupt_before_io (first : UInt8) (counter interruptions : Nat) (positive : 1 ≤ counter)
    (byte : first = 1 ∨ first = 7 ∨ first = 9) :
    Interrupted first counter (List.replicate interruptions (filesystem counter first)) counter := by
  have admitted : filesystemCrashImage names [(1, ⟨#[0, 0]⟩)] (registered (cold counter first)) =
      some (filesystem counter first) := by
    rcases byte with rfl | rfl | rfl <;> cbv
  induction interruptions with
  | zero => exact .done _
  | succ count ih =>
    refine .crash (elapsed := fun _ _ => 0) (chosen := names) (masks := [(1, ⟨#[0, 0]⟩)])
      Concurrent.Run.refl ?_ ih
    exact admitted

private theorem every_capture (first : UInt8) (byte : first = 1 ∨ first = 7 ∨ first = 9)
    (counter final : Nat) (positive : 1 ≤ counter)
    (images : List FilesystemImage) (attempts : Interrupted first counter images final) :
    counter ≤ final ∧ final ≤ counter + 6 * images.length ∧
      ∀ image ∈ images, image = filesystem image.highWater first ∧
        restartFilesystem image (reopenScript (serialImage first)) = some (cold image.highWater first) := by
  induction attempts with
  | done => simp
  | @crash counter final elapsed events last chosen masks image images run saved next ih =>
    obtain ⟨kept, lower, upper⟩ :=
      crash_during_reopen counter first positive byte elapsed run chosen masks image saved
    have live : 1 ≤ image.highWater := by omega
    obtain ⟨tailLower, tailUpper, tailSafe⟩ := ih live
    refine ⟨by omega, ?_, ?_⟩
    · simp only [List.length_cons]
      omega
    · intro candidate member
      rcases List.mem_cons.mp member with equal | rest
      · subst candidate
        have recorded : image.highWater = (snapshot last).nativeRefCounter :=
          congrArg FilesystemImage.highWater kept
        have exactImage : image = filesystem image.highWater first := by
          rw [recorded]
          exact kept
        refine ⟨exactImage, ?_⟩
        conv_lhs => rw [exactImage]
        exact (named_restart_reads elapsed image.highWater first live byte).1
      · exact tailSafe candidate rest

/-- Any finite number of admitted crashes during the actual named reopen/read
preserves the original persisted byte. Every terminal final retry returns that
byte with a fresh resource and the exact expected heap. -/
theorem every_finite_reopen (first : UInt8) (byte : first = 1 ∨ first = 7 ∨ first = 9)
    (counter final : Nat) (positive : 1 ≤ counter)
    (images : List FilesystemImage) (attempts : Interrupted first counter images final) :
    counter ≤ final ∧ final ≤ counter + 6 * images.length ∧
    (∀ image ∈ images, image = filesystem image.highWater first ∧
       restartFilesystem image (reopenScript (serialImage first)) = some (cold image.highWater first)) ∧
    ∀ (elapsed : PID → Nat → Nat) trace last result,
      Concurrent.Run (.start (registered (cold final first)) (reopen
        __OPEN__
        __OBSERVE__) elapsed) trace last →
      Concurrent.Terminal last result → accepted final first last = true := by
  obtain ⟨lower, upper, safe⟩ := every_capture first byte counter final positive images attempts
  refine ⟨lower, upper, safe, ?_⟩
  intro elapsed trace last result run terminal
  exact Concurrent.checkPost_sound
    (named_restart_reads elapsed final first (by omega) byte).2 run terminal

/-- The first crash can occur at any concurrent writer prefix. Its admitted
named image supplies the bytes for every subsequent interrupted reopen and the
final successful Rustler retry. -/
theorem named_crash_reopens_after_retries (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term}
    (run : Concurrent.Run (.start Positional.Concurrent.ready (Positional.Concurrent.program
      __PATCH__
      __OBSERVE__) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (saved : filesystemCrashImage chosen masks (snapshot last) = some image) :
    ∃ first, image = filesystem (snapshot last).nativeRefCounter first ∧
      (∀ images final (_ : Interrupted first image.highWater images final),
        image.highWater ≤ final ∧ final ≤ image.highWater + 6 * images.length ∧
        (∀ next ∈ images, next = filesystem next.highWater first ∧
          restartFilesystem next (reopenScript (serialImage first)) = some (cold next.highWater first)) ∧
        ∀ (retryClock : PID → Nat → Nat) trace done result,
          Concurrent.Run (.start (registered (cold final first)) (reopen
            __OPEN__
            __OBSERVE__) retryClock) trace done →
          Concurrent.Terminal done result → accepted final first done = true) ∧
      (∀ writer peer, NativeFile.lookup ⟨2⟩ (snapshot last) = some writer →
        NativeFile.lookup ⟨7⟩ (snapshot last) = some peer →
        Positional.CrashPrefix.synchronized writer peer = true →
        Positional.CrashPrefix.writtenByte first = true) := by
  obtain ⟨first, _, byte, kept, _, _, synced⟩ :=
    Positional.NamedCapture.named_crash_reopens elapsed run chosen masks image saved
  have bound := (Positional.NamedPrefix.retains_named_inode elapsed run).2.2.1
  have positive : 1 ≤ image.highWater := by
    rw [kept]
    change 1 ≤ (snapshot last).nativeRefCounter
    omega
  refine ⟨first, kept, ?_, synced⟩
  intro images final attempts
  exact every_finite_reopen first byte image.highWater final positive images attempts

end Positional.RepeatedReopen
