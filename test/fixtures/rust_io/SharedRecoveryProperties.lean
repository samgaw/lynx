module
public import Record.LogProperties
public import Record.ConstructedConcurrentProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.SharedRecoveryProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties
  Record.IntegrityProperties Record.CrashProperties Record.AppendProperties Record.LogProperties

/-- The crash image theorem depends on the file lookup, not its heap layout.
It therefore applies to shared inode/descriptor state as well as independent files. -/
theorem stable_lookup_image (file : NativeFile) (env : Environment)
    (state : State) (mask : ByteArray) (image : Image)
    (found : lookup file env = some state) (stable : state.durable = state.visible)
    (captured : crashImage file mask env = some image) :
    image.bytes = state.visible ∧ image.highWater = env.nativeRefCounter := by
  unfold crashImage at captured
  rw [found] at captured
  change (persist state.durable state.visible mask).bind (fun durable =>
    some (⟨durable, env.nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨durable, accepted, record⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj record
  exact ⟨persist_same state.visible mask durable (stable ▸ accepted), rfl⟩

/-- The actual extracted recovery loop returns every acknowledged payload from
an admitted synchronized inode image, irrespective of resource owners and locks
in the old machine. Reopening the image remains the stated host boundary. -/
theorem recover_shared_log (file : NativeFile) (env : Environment)
    (state : State) (values : List U16) (mask : ByteArray) (image : Image) (rest : Term)
    (found : lookup file env = some state) (stable : state.durable = state.visible)
    (contents : state.visible = disk (logBytes values)) (bounded : values.length ≤ 262144)
    (captured : crashImage file mask env = some image) :
    recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          (scanning image.bytes rest (4 * values.length)) []) := by
  have shape : image.bytes = disk (logBytes values) :=
    (stable_lookup_image file env state mask image found stable captured).1.trans contents
  rw [restart_as_fileEnv]
  simpa only [shape] using recover_encoded_log (⟨image.highWater + 1⟩ : NativeFile)
    ({} : Environment) [] values rest 0 (by simp [Separate]) bounded (by simp [limit])

/-- Recovery also applies to the actual constructor's inode/descriptor layout,
including every supported resource-owner phase and unrelated process state. -/
theorem constructed_log_recovery (env : Environment) (counter : Nat)
    (phase : Record.ConstructedConcurrentProperties.Phase) (mutex : Term)
    (state : State) (values : List U16) (mask : ByteArray) (image : Image) (rest : Term)
    (bound : 2 ≤ counter) (valid : Valid state) (stable : state.durable = state.visible)
    (contents : state.visible = disk (logBytes values)) (bounded : values.length ≤ 262144)
    (captured : crashImage ⟨2⟩ mask
      (Record.ConstructedConcurrentProperties.world env counter phase mutex state) = some image) :
    recover_log ⟨image.highWater + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (restarted image (recoveryScript image.bytes rest)) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
        fileEnv ({} : Environment) ⟨image.highWater + 1⟩
          (scanning image.bytes rest (4 * values.length)) []) := by
  exact recover_shared_log ⟨2⟩ _ state values mask image rest
    (Record.ConstructedConcurrentProperties.file_lookup env counter phase mutex state bound valid)
    stable contents bounded captured

end Record.SharedRecoveryProperties
