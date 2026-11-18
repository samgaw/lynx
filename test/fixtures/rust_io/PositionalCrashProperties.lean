module
public import Positional.Concurrent
public import Lynx.Concurrent
import Lynx.Runner.CheckPost
public section
open Aeneas Aeneas.Std Lynx Lynx.NativeFile

namespace Positional.CrashPrefix
open Positional.Concurrent (ready program)

@[expose] def snapshot : Concurrent.Config Term → Environment
  | .start env .. => env
  | .running state .. => state.nativeView []

@[expose] def writtenByte (byte : UInt8) : Bool := byte == 7 || byte == 9

@[expose] def imageWith (first : UInt8 → Bool) (bytes : ByteArray) : Bool :=
  bytes.size == 2 && first bytes[0]! && bytes[1]! == 2

@[expose] def allowedImage (bytes : ByteArray) : Bool :=
  imageWith (fun byte => byte == 1 || writtenByte byte) bytes

/-- The scripts have advanced past data synchronization for either descriptor.
The parent may still have its final observation queued. -/
@[expose] def synchronized (writer peer : NativeFile.State) : Bool :=
  (writer.script == .nil || (action "read_at" writer.script).isSome) || peer.script == .nil

@[expose] def retainsFile (config : Concurrent.Config Term) : Bool :=
  let env := snapshot config
  match NativeFile.lookup ⟨2⟩ env, NativeFile.lookup ⟨7⟩ env with
  | some writer, some peer =>
      allowedImage writer.durable && allowedImage writer.visible &&
        (!synchronized writer peer ||
          (imageWith writtenByte writer.durable && imageWith writtenByte writer.visible))
  | _, _ => false

private theorem persisted_byte (old visible mask result : ByteArray)
    (accepted : persist old visible mask = some result) (i : Nat) (inside : i < result.size) :
    result[i]! = if mask[i]! == 1 then visible[i]! else old[i]! := by
  unfold persist at accepted
  split at accepted
  · cases accepted
    have inbound : i < mask.size := by simpa [← ByteArray.size_data] using inside
    rw [getElem!_pos (⟨mask.data.mapIdx fun index choice =>
      if choice == 1 then visible[index]! else old[index]!⟩ : ByteArray) i inside,
      getElem!_pos mask i inbound]
    change (mask.data.mapIdx _)[i] = _
    simp only [_root_.Array.getElem_mapIdx]
    rfl
  · contradiction

private theorem persists_with (first : UInt8 → Bool) (old visible mask bytes : ByteArray)
    (durable : imageWith first old = true) (current : imageWith first visible = true)
    (accepted : persist old visible mask = some bytes) : imageWith first bytes = true := by
  simp only [imageWith, Bool.and_eq_true, beq_iff_eq] at durable current ⊢
  have size := Positional.Properties.persist_size old visible mask bytes accepted
  have minimum : min old.size visible.size ≤ mask.size := by
    unfold persist at accepted
    split at accepted
    · rename_i admitted
      exact admitted.1
    · contradiction
  have length : bytes.size = 2 := by
    rw [durable.1.1, current.1.1, Nat.min_self] at minimum
    have maximum : mask.size ≤ 2 := by
      simpa only [durable.1.1, current.1.1, Nat.max_self] using size.2
    omega
  refine ⟨⟨length, ?_⟩, ?_⟩
  · rw [persisted_byte _ _ _ _ accepted 0 (by omega)]
    split
    · exact current.1.2
    · exact durable.1.2
  · rw [persisted_byte _ _ _ _ accepted 1 (by omega)]
    split
    · exact current.2
    · exact durable.2

set_option maxRecDepth 8192 in
set_option maxHeartbeats 256000000 in
private theorem prefixes_checked (elapsed : PID → Nat → Nat) :
    Concurrent.checkInvariant retainsFile 64 (.start ready
      (program
        __PATCH__
        __OBSERVE__)
      elapsed) = true := by
  lynx_check_invariant

/-- Every admitted bytewise tear at every reached prefix retains the untouched
second byte. Once either synchronization has completed, the original first
byte is excluded from every admitted crash image. -/
theorem crashes_preserve_positional_bytes (elapsed : PID → Nat → Nat)
    (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start ready
      (program
        __PATCH__
        __OBSERVE__)
      elapsed) events last)
    (mask : ByteArray) (image : Image)
    (captured : crashImage ⟨2⟩ mask (snapshot last) = some image) :
    allowedImage image.bytes = true ∧
    ∀ writer peer, NativeFile.lookup ⟨2⟩ (snapshot last) = some writer →
      NativeFile.lookup ⟨7⟩ (snapshot last) = some peer →
      synchronized writer peer = true → imageWith writtenByte image.bytes = true := by
  have retained := Concurrent.checkInvariant_sound (prefixes_checked elapsed) run
  unfold retainsFile at retained
  cases found : NativeFile.lookup ⟨2⟩ (snapshot last) with
  | none => simp [found] at retained
  | some writer =>
    cases other : NativeFile.lookup ⟨7⟩ (snapshot last) with
    | none => simp [found, other] at retained
    | some peer =>
      simp only [found, other, Bool.and_eq_true] at retained
      unfold crashImage at captured
      rw [found] at captured
      change (persist writer.durable writer.visible mask).bind (fun bytes =>
        some (⟨bytes, (snapshot last).nativeRefCounter⟩ : Image)) = some image at captured
      obtain ⟨bytes, choice, result⟩ := Option.bind_eq_some_iff.mp captured
      cases Option.some.inj result
      refine ⟨persists_with _ _ _ _ _ retained.1.1 retained.1.2 choice, ?_⟩
      intro finalWriter finalPeer first second synced
      cases Option.some.inj first
      cases Option.some.inj second
      have keptAfterSync : imageWith writtenByte writer.durable = true ∧
          imageWith writtenByte writer.visible = true := by
        simpa only [synced, Bool.not_true, Bool.false_or, Bool.and_eq_true] using retained.2
      exact persists_with _ _ _ _ _ keptAfterSync.1 keptAfterSync.2 choice

end Positional.CrashPrefix

namespace Positional.CrashRead
open Positional.Properties
open Positional.Nif (zeros)

@[expose] def freshBuffer : Slice U8 := .from [0#u8] (by scalar_tac)

@[expose] def restartScript (image : Image) : Term :=
  outcome "read_at" true 1 (zeros image.bytes) .nil

private theorem zero_mask (bytes : ByteArray) : persist bytes bytes (zeros bytes) = some bytes := by
  have conditions : bytes.size ≤ (zeros bytes).size ∧
      (zeros bytes).size ≤ bytes.size ∧
      ((zeros bytes).data.toList.all (fun byte => byte == 0 || byte == 1)) = true := by
    simp [zeros, ← ByteArray.size_data]
  let result : ByteArray := ⟨(zeros bytes).data.mapIdx fun index choice =>
    if choice == 1 then bytes[index]! else bytes[index]!⟩
  have accepted : persist bytes bytes (zeros bytes) = some result := by
    unfold persist
    simp only [Nat.min_self, Nat.max_self]
    rw [ite_eq_left conditions]
  rwa [persist_same bytes (zeros bytes) result accepted] at accepted

private theorem read_single_byte (image : Image) (length : image.bytes.size = 2) :
    (readBuffer (⟨image.bytes, image.bytes, 0, restartScript image⟩ : NativeFile.State)
      freshBuffer 1 (by simp [freshBuffer]) (by simp [length])).val =
      [U8.ofNatCore image.bytes[0]!.toNat (by have := image.bytes[0]!.toNat_lt; scalar_tac)] := by
  have size : image.bytes.data.toList.length = 2 := by
    simpa only [_root_.Array.length_toList, ← ByteArray.size_data] using length
  cases cells : image.bytes.data.toList with
  | nil => simp [cells] at size
  | cons head tail =>
    have available : 0 < image.bytes.size := by omega
    have byte : image.bytes[0]! = head := by
      rw [getElem!_pos image.bytes 0 available]
      change image.bytes.data[0]'(by simpa only [← ByteArray.size_data] using available) = head
      have found := congrArg (fun xs : List UInt8 => xs[0]?) cells
      simpa only [_root_.Array.getElem?_toList, List.getElem?_cons_zero,
        getElem?_pos image.bytes.data 0 (by simpa [ByteArray.size_data] using available), Option.some.injEq] using found
    simp [readBuffer, freshBuffer, cells, byte]

/-- Restart retires the old descriptor and the actual positional Rust reader
returns the first persisted byte through a newly admitted file. -/
theorem observes_after_restart (image : Image) (length : image.bytes.size = 2) :
    ∃ file env after output,
      restart image (restartScript image) = some (file, env) ∧
      file.id = image.highWater + 1 ∧
      io_protocol.positional.observe file 0#u64 freshBuffer env =
        (.ok (.Ok 1#usize, output), after) ∧
      output.val = [U8.ofNatCore image.bytes[0]!.toNat
        (by have := image.bytes[0]!.toNat_lt; scalar_tac)] := by
  let file : NativeFile := ⟨image.highWater + 1⟩
  let before : NativeFile.State := ⟨image.bytes, image.bytes, 0, restartScript image⟩
  have bounded : image.bytes.size ≤ limit := by simp [length, limit]
  have valid : Valid before := by simp [Valid, before, bounded]
  have fits : 1 ≤ freshBuffer.val.length := by simp [freshBuffer]
  have available : 1 ≤ before.visible.size - (0#u64).val := by
    simp [before, length, U64.ofNat]
  have countOne : count freshBuffer 1 fits = 1#usize := by
    apply UScalar.eq_of_val_eq
    simp [count, Usize.ofNat]
  let result := readBuffer before freshBuffer 1 fits (by simp [before, length])
  refine ⟨file, fileEnv {} file before [], fileEnv {} file {before with script := .nil} [], result,
    ?_, rfl, ?_, ?_⟩
  · simp [restart, not_lt.mpr bounded, file, before, fileEnv]
  · have step := Positional.Proofs.observe_prefix file 0#u64 freshBuffer {} [] before
      1 (zeros image.bytes) image.bytes .nil (by simp [Separate]) valid
      (by scalar_tac) (by simp [freshBuffer, limit]) (by decide) fits available rfl
      (zero_mask image.bytes)
    simpa [countOne, before, U64.ofNat] using step
  · exact read_single_byte image length

end Positional.CrashRead

namespace Positional.CrashRecovery
open Positional.Concurrent (ready program)
open Positional.CrashPrefix Positional.CrashRead

/-- Every admitted crash at a raw prefix has a fresh-handle restart whose
actual positional read returns the persisted first byte. After either
successful data synchronization, that byte must have been written. -/
theorem crashes_recover_positional_byte (elapsed : PID → Nat → Nat)
    (events : List Concurrent.Event) (last : Concurrent.Config Term)
    (run : Concurrent.Run (.start ready
      (program
        __PATCH__
        __OBSERVE__)
      elapsed) events last)
    (mask : ByteArray) (image : Image)
    (captured : crashImage ⟨2⟩ mask (snapshot last) = some image) :
    ∃ file env after output,
      restart image (restartScript image) = some (file, env) ∧
      file.id = image.highWater + 1 ∧
      io_protocol.positional.observe file 0#u64 freshBuffer env =
        (.ok (.Ok 1#usize, output), after) ∧
      output.val = [U8.ofNatCore image.bytes[0]!.toNat
        (by have := image.bytes[0]!.toNat_lt; scalar_tac)] ∧
      allowedImage image.bytes = true ∧
      ∀ writer peer, NativeFile.lookup ⟨2⟩ (snapshot last) = some writer →
        NativeFile.lookup ⟨7⟩ (snapshot last) = some peer →
        synchronized writer peer = true → writtenByte image.bytes[0]! = true := by
  obtain ⟨allowed, keptAfterSync⟩ := crashes_preserve_positional_bytes elapsed events last run mask image captured
  have length : image.bytes.size = 2 := by
    have size := allowed
    simp only [allowedImage, imageWith, Bool.and_eq_true, beq_iff_eq] at size
    exact size.1.1
  obtain ⟨file, env, after, output, restarted, fresh, observed, returned⟩ :=
    observes_after_restart image length
  refine ⟨file, env, after, output, restarted, fresh, observed, returned, allowed, ?_⟩
  intro writer peer first second synced
  have kept := keptAfterSync writer peer first second synced
  simp only [imageWith, Bool.and_eq_true] at kept
  exact kept.1.2

end Positional.CrashRecovery
