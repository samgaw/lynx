module
public import Record.MixedRepairScripts
public import Record.TornSyncRecovery
import Lynx.Runner.NativeArithmetic

public section

open Aeneas Aeneas.Std Lynx io_native
namespace Record.MixedRepairWitness
open NativeFile
open scoped Lynx.NativeArithmetic
open Record.FallibleReopen (call environment journalName)
open Record.TornSyncFailure (withTail)
open Record.NamedJournalCrash (namedJournal names_equal)
open Record.MixedRepairScripts (start syncScript)
open Record.TornSyncRecovery (registered script cold repairState)

private def findPrefix (accept : Concurrent.Config Term → Bool) :
    Nat → Concurrent.Config Term → Option (List Concurrent.Event × Concurrent.Config Term)
  | 0, _ => none
  | fuel + 1, config =>
      if accept config then some ([], config)
      else
        match config.successors with
        | [] => none
        | (event, next) :: _ =>
          (findPrefix accept fuel next).map fun (events, last) => (event :: events, last)

private theorem findPrefix_sound {accept : Concurrent.Config Term → Bool} {fuel : Nat}
    {first last : Concurrent.Config Term} {events : List Concurrent.Event}
    (found : findPrefix accept fuel first = some (events, last)) :
    Concurrent.Run first events last ∧ accept last = true := by
  induction fuel generalizing first events last with
  | zero => simp [findPrefix] at found
  | succ fuel ih =>
    by_cases accepted : accept first = true
    · simp [findPrefix, accepted] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨.refl, accepted⟩
    · cases successors : first.successors with
      | nil => simp [findPrefix, accepted, successors] at found
      | cons edge others =>
        obtain ⟨event, next⟩ := edge
        simp only [findPrefix, if_neg accepted, successors, Option.map_eq_some_iff] at found
        obtain ⟨⟨trail, selected⟩, chosen, equal⟩ := found
        cases equal
        obtain ⟨run, accepted⟩ := ih chosen
        have step : Concurrent.Step first event next := by
          change (event, next) ∈ first.successors
          simp [successors]
        exact ⟨.step step run, accepted⟩

@[expose] def resizeMask : ByteArray := ⟨#[1,0,1,0,1,0,1,0,1,0]⟩
@[expose] def syncMask : ByteArray := ⟨#[0,0,0,0,0,0,0,0,0]⟩
@[expose] def closeMask : ByteArray := ⟨#[0,0,0,0,0,0,0,0]⟩
@[expose] def crashMask : List (Nat × ByteArray) := [(1, ⟨#[0,1,0,1,0,1,0,1,0,0]⟩)]

@[expose] def beforeFailedSync : Environment :=
  start 1 true [99,77,88] resizeMask syncMask closeMask false

@[expose] def interruptedImage : FilesystemImage :=
  ⟨namedJournal journalName, [(1, withTail true [0,77])], 3⟩

@[expose] def atResizeBoundary (last : Concurrent.Config Term) : Bool :=
  let env := environment last
  match getHandle ⟨3⟩ writableHandleTypeName env,
      filesystemCrashImage (namedJournal journalName) crashMask env with
  | some handle, some captured =>
    handle.script == syncScript 2 syncMask closeMask false &&
    !(last.successors.isEmpty) &&
    tablesEqual captured.names (namedJournal journalName) &&
    captured.inodes.map (fun entry => (entry.1, entry.2.data)) == [(1, (withTail true [0,77]).data)] &&
    captured.highWater == 3
  | _, _ => false

set_option maxRecDepth 8192 in
set_option maxHeartbeats 32000000 in
theorem interrupted_prefix_exists :
    ∃ events last,
      Concurrent.Run (.start beforeFailedSync (call __TRY_REOPEN__ 3#u32)) events last ∧
      atResizeBoundary last = true := by
  let first := Concurrent.Config.start beforeFailedSync (call __TRY_REOPEN__ 3#u32)
  have check : (findPrefix atResizeBoundary 64 first).isSome = true := by cbv
  cases selected : findPrefix atResizeBoundary 64 first with
  | none => simp [selected] at check
  | some path =>
    obtain ⟨events, last⟩ := path
    exact ⟨events, last, findPrefix_sound selected⟩

@[expose] def restartBoot : Environment := registered (cold 3 (withTail true [0,77]))

private theorem boundary_image (last : Concurrent.Config Term) (checked : atResizeBoundary last = true) :
    !(last.successors.isEmpty) = true ∧
      filesystemCrashImage (namedJournal journalName) crashMask (environment last) =
        some interruptedImage := by
  unfold atResizeBoundary at checked
  dsimp only at checked
  split at checked
  · rename_i handle captured opened found
    simp only [Bool.and_eq_true, beq_iff_eq] at checked
    obtain ⟨⟨⟨⟨_, alive⟩, named⟩, bytes⟩, high⟩ := checked
    refine ⟨alive, ?_⟩
    have contents : captured.inodes = [(1, withTail true [0,77])] := by
      cases nodes : captured.inodes with
      | nil => simp [nodes] at bytes
      | cons entry rest =>
        rw [nodes] at bytes
        simp only [List.map_cons, List.cons.injEq, List.map_eq_nil_iff, Prod.mk.injEq] at bytes
        have same : entry = (1, withTail true [0,77]) :=
          Prod.ext bytes.1.1 (ByteArray.ext bytes.1.2)
        simp [same, bytes.2]
    rw [found]
    have table := names_equal _ _ named
    cases captured
    simp_all [interruptedImage]
  · contradiction

set_option maxRecDepth 8192 in
/-- The interrupted boot for the retry uses the actual mixed-mask image after
truncation while synchronization remains pending and the descriptor is live. -/
theorem restart_from_witness :
    (∃ events last,
      Concurrent.Run (.start beforeFailedSync (call __TRY_REOPEN__ 3#u32)) events last ∧
      !(last.successors.isEmpty) = true ∧
      filesystemCrashImage (namedJournal journalName) crashMask (environment last) =
        some interruptedImage) ∧
    (restartFilesystem interruptedImage (script (withTail true [0,77]))).map registered =
      some restartBoot := by
  obtain ⟨events, last, ran, checked⟩ := interrupted_prefix_exists
  exact ⟨⟨events, last, ran, boundary_image last checked⟩, by cbv⟩

@[expose] def lawAccepted (last : Concurrent.Config Term) : Bool :=
  match last.outcome with
  | .ok (.atom "true") => repairState 3 true 10 (environment last)
  | _ => false

theorem law_outcome (last : Concurrent.Config Term) (checked : lawAccepted last = true) :
    last.outcome = .ok Term.true := by
  unfold lawAccepted at checked
  split at checked
  · assumption
  · contradiction

end Record.MixedRepairWitness
