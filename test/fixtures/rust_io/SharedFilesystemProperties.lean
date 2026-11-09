module
public import Record.SharedReadProperties
public import Record.ConstructedConcurrentProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
namespace Record.SharedFilesystemProperties
open NativeFile Record.Properties Record.RecoveryProperties Record.CrashProperties
  Record.LogProperties Record.SharedReadProperties

attribute [local simp] NativeCodec.typeName NativeCodec.encode NativeMutex.typeName
  NativeResourceArc.typeName NativeResourceArc.handleType NativeResourceArc.termType

/-- All resource-owner phases retain the synchronized journal name and inode.
The crash image drops descriptors, owners and locks rather than serializing them. -/
theorem constructed_image (env : Environment) (counter : Nat)
    (phase : Record.ConstructedConcurrentProperties.Phase) (mutex : Term) (state : State)
    (mask saved : ByteArray) (bound : 2 ≤ counter) (valid : Valid state)
    (stable : state.durable = state.visible)
    (accepted : persist state.durable state.visible mask = some saved) :
    filesystemCrashImage Record.ConstructorLogProperties.names [(1,mask)]
      (Record.ConstructedConcurrentProperties.world env counter phase mutex state) =
      some ⟨Record.ConstructorLogProperties.names,[(1,state.visible)],counter⟩ := by
  have same := persist_same state.visible mask saved (stable ▸ accepted)
  subst saved
  have decoded := Record.Properties.decode_encode {state with position := 0,script := .nil}
    ⟨valid.1,valid.2.1,Nat.zero_le _⟩
  have positive : ¬counter < 1 := by omega
  cases phase <;>
    simp [filesystemCrashImage,Record.ConstructedConcurrentProperties.world,
      Record.ConstructedConcurrentProperties.shared,Record.ConstructedConcurrentProperties.frame,
      Record.ConstructedConcurrentProperties.pinnedFrame,Record.ConstructedConcurrentProperties.decodedFrame,
      Record.ConstructedConcurrentProperties.overlappingFrame,Record.ConstructedConcurrentProperties.remainingFrame,
      NativeResourceArc.vmCells,Record.ConstructedConcurrentProperties.payload,
      Record.ConstructorLogProperties.payload,
      namespaceSnapshot,namespaceTable,namespaceHistory,namespaceEntry,tablesEqual,encodeNamespace,
      encodeNames,List.eraseDups_cons,namespaceCrashAllowed,namedInode,
      Record.ConstructorLogProperties.names,Record.ConstructorLogProperties.valid_fileName,
      inode,decoded,accepted,positive,inodeTypeName,namespaceTypeName,closedDirectoryTypeName,
      writableHandleTypeName,encodeHandle]


/-- A synchronized constructor-layout log survives the admitted filesystem crash
and is reopened and decoded by the actual Rust implementations. All old owner
and mutex phases lead to the same persistent image. -/
theorem constructed_filesystem_recovery (env : Environment) (counter : Nat)
    (phase : Record.ConstructedConcurrentProperties.Phase) (mutex : Term) (state : State)
    (values : List U16) (rest : Term) (mask saved : ByteArray)
    (bound : 2 ≤ counter) (valid : Valid state) (stable : state.durable = state.visible)
    (contents : state.visible = disk (logBytes values)) (bounded : values.length ≤ 262144)
    (accepted : persist state.durable state.visible mask = some saved) :
    let data := disk (logBytes values)
    let script := recoveryScript data rest
    filesystemCrashImage Record.ConstructorLogProperties.names [(1,mask)]
      (Record.ConstructedConcurrentProperties.world env counter phase mutex state) =
      some ⟨Record.ConstructorLogProperties.names,[(1,data)],counter⟩ ∧
    restartFilesystem ⟨Record.ConstructorLogProperties.names,[(1,data)],counter⟩
      (openingScript script) = some (boot counter data script) ∧
    io_core.open_readonly (toStr "journal") (boot counter data script) =
      (.ok (.Ok ⟨counter + 1⟩),
        reopened counter Record.ConstructorLogProperties.names ⟨data,data,0,script⟩) ∧
    recover_log ⟨counter + 1⟩ (Usize.ofNatCore values.length (by scalar_tac))
      (reopened counter Record.ConstructorLogProperties.names ⟨data,data,0,script⟩) =
      (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)),⟨counter + 1⟩),
        reopened counter Record.ConstructorLogProperties.names
          (scanning data rest (4 * values.length))) := by
  dsimp only
  refine ⟨?_,named_log_restart counter values rest (by omega) bounded⟩
  simpa only [contents] using constructed_image env counter phase mutex state mask saved
    bound valid stable accepted

end Record.SharedFilesystemProperties
