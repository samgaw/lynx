module
public import Record.MixedRepairScripts
public import Record.TornSyncRecovery
import Lynx.Runner.NativeArithmetic
public meta import Lean

public section

open Aeneas Aeneas.Std Lynx io_native

namespace Record.MixedRepairRecovery
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (contents call environment journalName)
open Record.TornSyncFailure (withTail preserves rejected tail_forms)
open Record.NamedJournalCrash (inodeIds namedJournal names_equal captured_journal JournalBytes persist_journal)
open Record.MixedRepairScripts (start)
open Record.TornSyncRecovery (image_shape script cold repaired registered reopens_captured_image)

-- The certificate observes what the given host mask actually persisted.
structure Choice (old visible result : ByteArray) where
  mask : ByteArray
  accepted : persist old visible mask = some result

@[expose, cbv_opaque] def mask {old visible result : ByteArray}
    (choice : Choice old visible result) : ByteArray :=
  choice.mask

theorem persist_choice {old visible result : ByteArray}
    (choice : Choice old visible result) :
    persist old visible (mask choice) = some result :=
  choice.accepted

section
open Lean Meta

-- This rewrite applies only to the exact persistence call established by the
-- certificate. Unrecognized calls use the standard reduction.
scoped cbv_simproc cbv_eval applyChoice (persist _ _ _) := fun expr => do
  let args := expr.getAppArgs
  let selected := args[2]!
  if !selected.isAppOfArity ``mask 4 then return .rfl
  let proof ← mkAppM ``persist_choice #[selected.appArg!]
  let equality := (← inferType proof).getAppArgs
  if ← withTransparency .all (isDefEq expr equality[1]!) then
    return .step equality[2]! proof
  else return .rfl

end

open scoped Record.MixedRepairRecovery

private theorem head_size (left : Bool) : (contents left).size = 8 := by
  cases left <;> rfl

private theorem packed_size (left : Bool) (tail : List UInt8) :
    (withTail left tail).size = 8 + tail.length := by
  change ((contents left).data ++ tail.toArray).size = _
  have head : (contents left).data.size = 8 := head_size left
  rw [_root_.Array.size_append, head, List.size_toArray]

private theorem packed_image (left : Bool) (tail : List UInt8) (short : tail.length < 4) :
    JournalBytes (contents left) (withTail left tail) := by
  refine ⟨⟨by rw [head_size, packed_size]; omega, ?_⟩, by rw [head_size, packed_size]; omega⟩
  intro i inside
  have inTail : i < (withTail left tail).size := by
    rw [packed_size]
    rw [head_size] at inside
    omega
  rw [getElem!_pos (withTail left tail) i inTail, getElem!_pos (contents left) i inside]
  simp [withTail, ByteArray.getElem_eq_getElem_data, _root_.Array.getElem_append_left, inside]

private theorem sync_image (left : Bool) :
    JournalBytes (contents left) (contents left) :=
  ⟨⟨le_rfl, fun _ _ => rfl⟩, by omega⟩

private theorem persisted_size (old visible mask result : ByteArray)
    (prior : visible.size ≤ old.size) (accepted : persist old visible mask = some result) :
    result.size ≤ old.size := by
  unfold persist at accepted
  split at accepted
  · rename_i sizes
    have upper : mask.size ≤ old.size := sizes.2.1.trans_eq (max_eq_left prior)
    cases accepted
    simpa [← ByteArray.size_data] using upper
  · contradiction

@[expose] def keepsJournal (counter : Nat) (left : Bool) (config : Concurrent.Config Term) : Bool :=
  let env := environment config
  let names := namedJournal journalName
  counter ≤ env.nativeRefCounter && inodeIds env == [1] &&
  (match namespaceSnapshot env, inode 1 env with
   | some table, some file => tablesEqual table.names names && tablesEqual table.committed names &&
     table.pending.isEmpty && preserves left file.visible && preserves left file.durable
   | _, _ => false)

@[expose] def repairChecked (counter : Nat) (left : Bool) (eof closeTail : Nat)
    (last : Concurrent.Config Term) : Bool :=
  keepsJournal counter left last &&
    (!last.successors.isEmpty || rejected counter left eof closeTail last)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 256000000 in
/-- Kernel reduction follows each admitted persistence result without branching
over the mask bytes. The masks remain the original host choices. -/
private theorem checked_masks (counter : Nat) (left closeSucceeds : Bool)
    (tail resized synchronized closed : List UInt8)
    (short : tail.length < 4) (resizedShort : resized.length < 4)
    (syncShort : synchronized.length < 4) (closedShort : closed.length < 4)
    (resizeBound : resized.length ≤ tail.length) (syncBound : synchronized.length ≤ resized.length)
    (closeBound : closed.length ≤ synchronized.length)
    (resizeChoice : Choice (withTail left tail) (contents left) (withTail left resized))
    (syncChoice : Choice (withTail left resized) (contents left) (withTail left synchronized))
    (closeChoice : Choice (withTail left synchronized) (contents left) (withTail left closed))
    (positive : 1 ≤ counter) (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant (repairChecked counter left tail.length closed.length) 64
      (.start (start counter left tail (mask resizeChoice) (mask syncChoice) (mask closeChoice) closeSucceeds)
        (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  rcases tail_forms tail short with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    rcases tail_forms resized resizedShort with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    rcases tail_forms synchronized syncShort with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    rcases tail_forms closed closedShort with rfl | ⟨_, rfl⟩ | ⟨_, _, rfl⟩ | ⟨_, _, _, rfl⟩ <;>
    simp only [List.length_nil, List.length_cons] at resizeBound syncBound closeBound
  all_goals first | omega | cases left <;> cases closeSucceeds <;> cbv

/-- Under every admitted resize, failed-sync and close mask the actual typed
repair preserves the named prefix at every step and releases both owners
before returning the typed error. -/
theorem all_admitted_masks (counter : Nat) (left closeSucceeds : Bool) (tail : List UInt8)
    (short : tail.length < 4) (resizeMask syncMask closeMask resized synchronized closed : ByteArray)
    (resizeChoice : persist (withTail left tail) (contents left) resizeMask = some resized)
    (syncChoice : persist resized (contents left) syncMask = some synchronized)
    (closeChoice : persist synchronized (contents left) closeMask = some closed)
    (positive : 1 ≤ counter) (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant (repairChecked counter left tail.length (closed.size - 8)) 64
      (.start (start counter left tail resizeMask syncMask closeMask closeSucceeds)
        (call __TRY_REOPEN__ 3#u32) elapsed) = true := by
  have complete := sync_image left
  have original := packed_image left tail short
  have resizedImage := persist_journal _ _ _ _ _ original complete resizeChoice
  have synchronizedImage := persist_journal _ _ _ _ _ resizedImage complete syncChoice
  have closedImage := persist_journal _ _ _ _ _ synchronizedImage complete closeChoice
  have resizeBound := persisted_size _ _ _ _ original.1.1 resizeChoice
  have syncBound := persisted_size _ _ _ _ resizedImage.1.1 syncChoice
  have closeBound := persisted_size _ _ _ _ synchronizedImage.1.1 closeChoice
  obtain ⟨resizeTail, resizeShort, rfl⟩ := image_shape left resized resizedImage
  obtain ⟨syncTail, syncShort, rfl⟩ := image_shape left synchronized synchronizedImage
  obtain ⟨closeTail, closeShort, rfl⟩ := image_shape left closed closedImage
  simp only [packed_size, Nat.add_le_add_iff_left] at resizeBound syncBound closeBound
  rw [packed_size, Nat.add_sub_cancel_left]
  exact checked_masks counter left closeSucceeds tail resizeTail syncTail closeTail
    short resizeShort syncShort closeShort resizeBound syncBound closeBound
    ⟨resizeMask, resizeChoice⟩ ⟨syncMask, syncChoice⟩ ⟨closeMask, closeChoice⟩ positive elapsed

private theorem retained_bytes (left : Bool) (bytes : ByteArray)
    (kept : preserves left bytes = true) : JournalBytes (contents left) bytes := by
  have head : (contents left).size = 8 := by cases left <;> rfl
  simp only [preserves, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at kept
  rw [JournalBytes, head]
  exact ⟨⟨kept.1.1, kept.2⟩, kept.1.2⟩

/-- Any admitted crash at a protected prefix keeps the original name and its
complete records. The retained image has only a possible partial next record. -/
private theorem prefix_crash (counter : Nat) (left : Bool) (config : Concurrent.Config Term)
    (safe : keepsJournal counter left config = true)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (environment config) = some image) :
    ∃ bytes, image = ⟨namedJournal journalName, [(1, bytes)], image.highWater⟩ ∧
      counter ≤ image.highWater ∧ JournalBytes (contents left) bytes := by
  unfold keepsJournal at safe
  dsimp only at safe
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at safe
  obtain ⟨⟨advance, ids⟩, images⟩ := safe
  split at images
  · rename_i table file snapshot found
    simp only [Bool.and_eq_true, List.isEmpty_iff] at images
    obtain ⟨⟨⟨⟨visible, committed⟩, pending⟩, current⟩, durable⟩ := images
    have named : namespaceSnapshot (environment config) =
        some ⟨namedJournal journalName, namedJournal journalName, [], table.script⟩ := by
      rw [snapshot]
      have live := names_equal _ _ visible
      have stable := names_equal _ _ committed
      cases table
      simp_all
    obtain ⟨mask, bytes, accepted, captured⟩ :=
      captured_journal journalName _ file table.script named ids found chosen masks image crash
    exact ⟨bytes, by rw [captured], by simpa only [captured] using advance,
      persist_journal _ _ _ _ _ (retained_bytes left _ durable) (retained_bytes left _ current) accepted⟩
  · contradiction

/-- Every admitted crash at any point of a modeled mixed-mask failed repair
can be recovered by the actual typed NIF under a successful host script. -/
theorem reopens_after_prefix_crash (counter : Nat) (left closeSucceeds : Bool) (tail : List UInt8)
    (short : tail.length < 4) (resizeMask syncMask closeMask resized synchronized closed : ByteArray)
    (resizeChoice : persist (withTail left tail) (contents left) resizeMask = some resized)
    (syncChoice : persist resized (contents left) syncMask = some synchronized)
    (closeChoice : persist synchronized (contents left) closeMask = some closed)
    (positive : 1 ≤ counter) (elapsed nextElapsed : PID → Nat → Nat)
    (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (ran : Concurrent.Run
      (.start (start counter left tail resizeMask syncMask closeMask closeSucceeds)
        (call __TRY_REOPEN__ 3#u32) elapsed) events last)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (crash : filesystemCrashImage chosen masks (environment last) = some image) :
    ∃ bytes, image = ⟨namedJournal journalName, [(1, bytes)], image.highWater⟩ ∧
      counter ≤ image.highWater ∧ JournalBytes (contents left) bytes ∧
      restartFilesystem image (script bytes) = some (cold image.highWater bytes) ∧
      Concurrent.checkPost (repaired image.highWater left bytes.size) 64
        (.start (registered (cold image.highWater bytes))
          (call __TRY_REOPEN__ 3#u32) nextElapsed) = true := by
  have checked := all_admitted_masks counter left closeSucceeds tail short resizeMask
    syncMask closeMask resized synchronized closed resizeChoice syncChoice closeChoice positive elapsed
  have observed := Concurrent.checkInvariant_sound checked ran
  simp only [repairChecked, Bool.and_eq_true] at observed
  obtain ⟨bytes, stored, advance, shape⟩ :=
    prefix_crash counter left last observed.1 chosen masks image crash
  obtain ⟨restart, restarted⟩ :=
    reopens_captured_image image.highWater left bytes (Nat.le_trans positive advance) shape nextElapsed
  refine ⟨bytes, stored, advance, shape, ?_, restarted⟩
  rw [← show image = ⟨Record.TornSyncRecovery.names, [(1, bytes)], image.highWater⟩ from stored] at restart
  exact restart

end Record.MixedRepairRecovery
