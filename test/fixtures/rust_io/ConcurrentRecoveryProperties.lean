module
public import Record.ConcurrentStorageProperties
public import Record.SharedRecoveryProperties
public section
open Aeneas Aeneas.Std Lynx io_native io_native.io_protocol
-- Evaluate the proved effect-tree contracts instead of re-expanding Rust
-- control flow and protocol arithmetic separately in every scheduler branch.
attribute [cbv_eval] Record.OverlappingLogProperties.caller_contract
  Record.RollbackProperties.append_contract

namespace Record.ConcurrentRecoveryProperties
open NativeFile Record.Properties Record.CrashProperties Record.RecoveryProperties
  Record.LogProperties Record.SharedRecoveryProperties

@[expose] def terminalEnvironment : Concurrent.Config Term → Environment
  | .start env _ => env
  | .running state .. => state.nativeView []

/-- Require both acknowledgements and complete synchronized records. The visible
and durable images must agree before composing with arbitrary crash choices. -/
@[expose] def recoverable (config : Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.atom "true") =>
    match NativeFile.lookup ⟨2⟩ (terminalEnvironment config) with
    | some file => file.visible.data == file.durable.data &&
      (file.durable.data == Record.ConcurrentStorageProperties.ordered.data ||
        file.durable.data == Record.ConcurrentStorageProperties.reversed.data)
    | none => false
  | _ => false

private theorem ordered_bytes : disk (logBytes [13#u16, 19#u16]) =
    Record.ConcurrentStorageProperties.ordered := by decide +kernel
private theorem reversed_bytes : disk (logBytes [19#u16, 13#u16]) =
    Record.ConcurrentStorageProperties.reversed := by decide +kernel

/-- Every admitted power-loss image of an accepted terminal state is recovered
by the actual extracted Rust loop in one of the two allowed serialization orders.
Fresh reopening and successful seek/read scripts remain explicit host admission. -/
theorem accepted_recovery (config : Concurrent.Config Term) (mask : ByteArray)
    (image : Image) (rest : Term) (accepted : recoverable config = true)
    (captured : crashImage ⟨2⟩ mask (terminalEnvironment config) = some image) :
    ∃ (values : List U16) (_bounded : values.length ≤ 262144), (values = [13#u16, 19#u16] ∨ values = [19#u16, 13#u16]) ∧
      recover_log ⟨image.highWater + 1⟩ 2#usize
        (restarted image (recoveryScript image.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            (scanning image.bytes rest (4 * values.length)) []) := by
  unfold recoverable at accepted
  split at accepted
  · split at accepted
    · rename_i file found
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at accepted
      obtain ⟨stableData, order⟩ := accepted
      have stable : file.visible = file.durable := ByteArray.ext stableData
      rcases order with orderedData | reversedData
      · have ordered : file.durable = Record.ConcurrentStorageProperties.ordered := ByteArray.ext orderedData
        refine ⟨[13#u16,19#u16], by decide, Or.inl rfl, ?_⟩
        have proof := recover_shared_log ⟨2⟩ (terminalEnvironment config) file
          [13#u16,19#u16] mask image rest found stable.symm
          (stable.trans (ordered.trans ordered_bytes.symm)) (by decide) captured
        simpa [Usize.ofNatCore] using proof
      · have reversed : file.durable = Record.ConcurrentStorageProperties.reversed := ByteArray.ext reversedData
        refine ⟨[19#u16,13#u16], by decide, Or.inr rfl, ?_⟩
        have proof := recover_shared_log ⟨2⟩ (terminalEnvironment config) file
          [19#u16,13#u16] mask image rest found stable.symm
          (stable.trans (reversed.trans reversed_bytes.symm)) (by decide) captured
        simpa [Usize.ofNatCore] using proof
    · contradiction
  · contradiction


theorem accepted_outcome (config : Concurrent.Config Term)
    (accepted : recoverable config = true) : config.outcome = .ok Term.true := by
  unfold recoverable at accepted
  split at accepted
  · assumption
  · contradiction

/-- Compose a checked concurrent computation with implementation-linked recovery
for every terminal run and every admitted post-acknowledgement crash image. -/
theorem checked_recovery {env : Environment} {computation : Result Term} {depth : Nat}
    {last : Concurrent.Config Term} {events : List Concurrent.Event} {outcome : Outcome Term}
    (verified : Concurrent.checkPost recoverable depth (.start env computation) = true)
    (run : Concurrent.Run (.start env computation) events last)
    (terminal : Concurrent.Terminal last outcome)
    (mask : ByteArray) (image : Image) (rest : Term)
    (captured : crashImage ⟨2⟩ mask (terminalEnvironment last) = some image) :
    ∃ (values : List U16) (_bounded : values.length ≤ 262144), (values = [13#u16, 19#u16] ∨ values = [19#u16, 13#u16]) ∧
      recover_log ⟨image.highWater + 1⟩ 2#usize
        (restarted image (recoveryScript image.bytes rest)) =
        (.ok (.Ok (alloc.vec.Vec.from values (by scalar_tac)), ⟨image.highWater + 1⟩),
          fileEnv ({} : Environment) ⟨image.highWater + 1⟩
            (scanning image.bytes rest (4 * values.length)) []) := by
  exact accepted_recovery last mask image rest
    (Concurrent.checkPost_sound verified run terminal) captured

/-- Buffered bytes differing from durable bytes cannot satisfy the recovery
postcondition, even when the durable image has both expected records. -/
theorem unsynchronized_image_rejected :
    recoverable (.start
      (Record.ConstructedConcurrentProperties.world {} 12 .pinned
        Record.ConstructedConcurrentProperties.free
        ⟨Record.ConcurrentStorageProperties.reversed,
          Record.ConcurrentStorageProperties.ordered, 8, .nil⟩)
      (.ok Term.true)) = false := by cbv

end Record.ConcurrentRecoveryProperties
