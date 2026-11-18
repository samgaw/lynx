module
public import Record.ConcurrentRollback
public import Record.RepeatedRepairProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.SerialRepair
open NativeFile Record.ConcurrentRollback Record.RepeatedRepairProperties
open Record.CrashProperties (disk)
open Record.LogProperties (logBytes)
open Record.Properties (fileEnv Separate)
open Record.ResizeProperties (lookup_admitted)
open Record.ReopenedLogProperties (finalEnvironment names)
open Record.RecoveryProperties (restarted)
open Record.RepairCrashProperties (log_image pending_image)

private theorem exactCrashes (values : List U16) (capacity : values.length ≤ 262144)
    (maxRecords : Usize) (count : Nat) (before after : Image)
    (contents : before.bytes = disk (logBytes values)) (bounded : before.bytes.size ≤ limit)
    (trace : RepairCrashes repair_log values capacity maxRecords count before after) :
    after.bytes = before.bytes ∧ after.highWater = before.highWater + count := by
  induction count generalizing before with
  | zero =>
    cases trace
    exact ⟨rfl, by omega⟩
  | succ count ih =>
    obtain ⟨middle, ⟨tail, resizeMask, durable, crashMask, rest, encoded, short, resized,
      _, _, caught⟩, remaining⟩ := trace
    have bound : (logBytes values ++ tail).length ≤ limit := by
      simpa [encoded, disk, ← ByteArray.size_data] using bounded
    have valid := (pending_image values tail resizeMask durable (.cons (.atom "blocked") rest)
      short bound (by simpa only [← encoded] using resized)).1
    have synced := persist_same _ resizeMask durable (by simpa only [← contents] using resized)
    unfold interruptedEnv crashImage at caught
    rw [lookup_admitted ({} : Environment) ⟨before.highWater + 1⟩ _ []
      (by simp [Separate]) valid] at caught
    change (persist durable (disk (logBytes values)) crashMask).bind
      (fun bytes => some (⟨bytes, max 0 (before.highWater + 1)⟩ : Image)) = some middle at caught
    rw [synced, ← contents] at caught
    obtain ⟨bytes, persisted, represented⟩ := Option.bind_eq_some_iff.mp caught
    have same := persist_same _ _ _ persisted
    rw [same, Nat.zero_max] at represented
    have exactImage := Option.some.inj represented
    subst middle
    obtain ⟨sameBytes, watermark⟩ := ih ⟨before.bytes, before.highWater + 1⟩ contents bounded remaining
    exact ⟨sameBytes, by dsimp only at watermark; omega⟩

private theorem recordCount (leftFirst : Bool) : (serialOrder leftFirst).log.length = 2 := by
  cases leftFirst <;> decide

private theorem fits (leftFirst : Bool) : (serialOrder leftFirst).log.length ≤ 262144 := by
  rw [recordCount]; decide

/-- A crash after the two replies matches the same serial order's disk image.
Any finite chain of actual interrupted repairs keeps that exact image, and a
successful retry returns those same records through a fresh file capability. -/
theorem retry_serial_log (elapsed : PID → Nat → Nat)
    {events : List Concurrent.Event} {last : Concurrent.Config Term} {outcome : Outcome Term}
    (run : Concurrent.Run (.start initial (reopenAndWrite __REOPEN__ __APPEND__) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome)
    (chosen : Names) (masks : List (Nat × ByteArray)) (image : FilesystemImage)
    (captured : filesystemCrashImage chosen masks (finalEnvironment last) = some image)
    (rest : Term) :
    ∃ leftFirst, let result := serialOrder leftFirst
      let bytes := disk (logBytes result.log)
      let before : Image := ⟨bytes, image.highWater⟩
      outcome = .ok result.reply ∧
      image = ⟨names, [(1, bytes)], (finalEnvironment last).nativeRefCounter⟩ ∧
      ∀ count,
        (∃ after, RepairCrashes repair_log result.log (by cases leftFirst <;> decide) 3#usize count before after) ∧
        ∀ after, RepairCrashes repair_log result.log (by cases leftFirst <;> decide) 3#usize count before after →
          after.bytes = bytes ∧ after.highWater = image.highWater + count ∧
          let file : NativeFile := ⟨after.highWater + 1⟩
          repair_log file 3#usize (restarted after (repairScript after.bytes rest)) =
            (.ok (.Ok (some (alloc.vec.Vec.from result.log (by
              have capacity : (serialOrder leftFirst).log.length ≤ 262144 := by cases leftFirst <;> decide
              scalar_tac))), file),
              fileEnv {} file ⟨bytes, bytes, bytes.size, rest⟩ []) := by
  obtain ⟨leftFirst, reply, named, _⟩ := recover_serial_log elapsed run terminal chosen masks image captured rest
  let values := (serialOrder leftFirst).log
  let bytes := disk (logBytes values)
  let before : Image := ⟨bytes, image.highWater⟩
  have shape : Record.RepairCrashProperties.LogImage values before.bytes := by
    simpa [before, bytes] using log_image values [] (by decide)
  have bound : before.bytes.size ≤ limit := by
    change (disk (logBytes (serialOrder leftFirst).log)).size ≤ limit
    cases leftFirst <;> decide +kernel
  have enough : values.length < (3#usize : Usize).val := by
    change (serialOrder leftFirst).log.length < (3#usize : Usize).val
    rw [recordCount]; decide +kernel
  refine ⟨leftFirst, reply, named, fun count => ⟨?_, ?_⟩⟩
  · obtain ⟨after, trace, _⟩ := interruptions_witness values (fits leftFirst) _ count before shape bound enough
    exact ⟨after, trace⟩
  · intro after trace
    obtain ⟨same, watermark⟩ := exactCrashes values (fits leftFirst) _ count before after rfl bound trace
    refine ⟨same, watermark, ?_⟩
    have checked := retry_after_interruptions values (fits leftFirst) _ count before after rest
      shape bound enough trace
    simpa only [same] using checked

end Record.SerialRepair
