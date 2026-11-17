module
public import Disk.Properties
public section
open Aeneas Aeneas.Std Lynx io_protocol
open NativeFile Disk.Properties
namespace Disk.DataSyncProperties

/-- A completed write and data sync locks in the acknowledged bytes and length
for every subsequent crash mask the regular-file model admits. -/
theorem acknowledged_crash (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term)) (before : State)
    (value : Nat) (mask durable syncMask : ByteArray) (rest : Term)
    (separate : Separate file frame) (valid : Valid before)
    (bounded : value ≤ data.val.length) (buffer : data.val.length ≤ limit)
    (position : before.position + value ≤ limit)
    (script : before.script = outcome "write" true value mask
      (outcome "sync_data" true 0 syncMask rest))
    (accepted : persist before.durable
      (overwrite before.visible before.position (bytes data) value) mask = some durable) :
    ∃ after, write_then_sync file data (fileEnv env file before frame) =
      (.ok (.Ok (count data value bounded), file), after) ∧
      ∀ crashMask image, crashImage file crashMask after = some image →
        image.bytes = overwrite before.visible before.position (bytes data) value := by
  let synced := overwrite before.visible before.position (bytes data) value
  let state : State := ⟨synced, synced, before.position + value, rest⟩
  refine ⟨fileEnv env file state frame,
    protocol_success file data env frame before value mask durable syncMask rest
      separate valid bounded buffer position script accepted, ?_⟩
  intro crashMask image captured
  have writtenBound :=
    (written_valid before data value mask durable rest valid bounded position accepted).1
  have stateValid : Valid state := ⟨writtenBound, Nat.le_refl _, position⟩
  unfold crashImage at captured
  rw [lookup_at env file state frame separate stateValid] at captured
  change (persist synced synced crashMask).bind (fun saved =>
    some (⟨saved, (fileEnv env file state frame).nativeRefCounter⟩ : Image)) = some image at captured
  obtain ⟨saved, choice, result⟩ := Option.bind_eq_some_iff.mp captured
  cases Option.some.inj result
  exact persist_same _ _ _ choice

/-- Even a valid directory-sync outcome cannot advance the namespace using this
Rust data-only call. The unsupported capability exhausts with the same state. -/
theorem directory_exhausts (namespaceState : NamespaceSnapshot) (rest : Term) :
    let env : Environment := {
      nativeRefCounter := 1
      nativeHeap := [(1, directoryTypeName, .tuple #[outcome "sync_dir" true 0 ByteArray.empty rest]),
        (0, namespaceTypeName, encodeNamespace namespaceState)] }
    io_core.synchronize ⟨1⟩ env = (.error .exhausted, env) := by
  intro env
  have rejected : pollSync ⟨1⟩ env true = some (.error .exhausted, env) := by
    simp [env, pollSync, lookup, directoryTypeName, typeName, handleTypeName,
      writableHandleTypeName]
  simp only [io_core.synchronize, monadLift_self, syncData]
  rw [Result.wait_ready_run _ _ _ _ _ rejected]
  simp [Result.error_apply]

end Disk.DataSyncProperties
