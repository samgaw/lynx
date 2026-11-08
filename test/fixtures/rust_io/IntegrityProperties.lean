module
public import Record.RecoveryProperties
public import Mathlib.Tactic.IntervalCases
public import Aeneas.Data.BitVec
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.IntegrityProperties
open NativeFile Record.Properties Record.ReadProperties Record.RecoveryProperties

attribute [local implicit_reducible] UScalar.cMax UScalar.rMax U32.rMax U8.rMax U16.rMax
theorem word_bv (a b : U8) : (word a b).bv = b.bv ++ a.bv := by
  apply (BitVec.eq_iff _ _).mpr
  intro i hi
  simp only [word, core.num.U16.from_le_bytes, U16.bv,
    BitVec.getElem!_cast, BitVec.fromLEBytes_getElem!]
  change Byte.testBit (((Aeneas.Std.Array.make 2#usize [a, b]).val.map U8.bv)[i / 8]!) (i % 8) = _
  rw [Aeneas.Std.Array.make_val]
  interval_cases i <;> simp only [Nat.reduceDiv, Nat.reduceMod, List.map_cons, List.map_nil,
    List.getElem!_cons_zero, List.getElem!_cons_succ,
    BitVec.getElem!_eq_testBit_toNat] <;> bv_normalize

@[expose] def low (value : U16) : U8 := ⟨value.bv.setWidth 8⟩
@[expose] def high (value : U16) : U8 := ⟨(value.bv >>> 8).setWidth 8⟩
@[expose] def layout (value : U16) : Array U8 4#usize :=
  Array.make 4#usize [low value, high value, low (~~~value), high (~~~value)]

/-- The record layout is computed by the actual internal Rust implementation. -/
theorem encode_spec (value : U16) : io_core.encode_record value = NativeM.ok (layout value) := by
  simp [io_core.encode_record, NativeM.lift, NativeM.ok, Array.index_usize,
    core.num.U16.to_le_bytes, BitVec.toLEBytes, NativeM.monadLift_eq, NativeM.fromRust,
    layout, low, high, UScalar.not]

/-- This equation is derived from the actual Rust check, not an assumed decoder. -/
theorem decode_spec (value inverse : U16) :
    io_core.decode_record value inverse = NativeM.ok
      (if value ^^^ inverse = core.num.U16.MAX then some value else none) := by
  by_cases h : value ^^^ inverse = core.num.U16.MAX <;>
    simp [io_core.decode_record, NativeM.lift, NativeM.ok, h]

@[expose] def selected (persisted : Bool) (byte : U8) : U8 := if persisted then byte else 0#u8

private theorem ones_bit (i : Nat) (h : i < 16) : (65535#16).getLsbD i = true := by
  interval_cases i <;> decide

/-- In a fresh record slot, zero/new byte tearing cannot produce a different
accepted value, including the degenerate all-zero and all-one input bytes. -/
theorem torn_decode (value : U16) (a b c d : Bool) :
    io_core.decode_record (word (selected a (low value)) (selected b (high value)))
      (word (selected c (low (~~~value))) (selected d (high (~~~value)))) = NativeM.ok none ∨
    io_core.decode_record (word (selected a (low value)) (selected b (high value)))
      (word (selected c (low (~~~value))) (selected d (high (~~~value)))) = NativeM.ok (some value) := by
  simp only [decode_spec]
  split
  · rename_i valid
    right
    have bits := congrArg UScalar.bv valid
    have equal : (word (selected a (low value)) (selected b (high value))).bv = value.bv := by
      cases a <;> cases b <;> cases c <;> cases d
      all_goals
        simp only [selected, Bool.false_eq_true, if_false, if_true, word_bv,
          low, high, UScalar.bv_xor, UScalar.bv_not, core.num.U16.MAX,
          UScalar.ofNat, UScalar.ofNatCore_bv, U16.rMax, UScalarTy.numBits] at bits ⊢
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have bit := congrArg (fun (x : BitVec 16) => x.getLsbD i) bits
        rw [ones_bit i hi] at bit
        interval_cases i <;>
          simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append, BitVec.getLsbD_setWidth,
            BitVec.getLsbD_ushiftRight, BitVec.getLsbD_not, BitVec.getLsbD_ofNat] at bit ⊢ <;>
          simp_all
    have same : word (selected a (low value)) (selected b (high value)) = value := by
      apply UScalar.eq_of_val_eq
      exact congrArg BitVec.toNat equal
    rw [same]
  · left
    rfl


/-- Execute both extracted reads before a caller continuation. -/
theorem word_next (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (before middle after : State) (lo hi : U8)
    (separate : Separate file frame) (valid : Valid before) (validMiddle : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (first : readStep before (one 0#u8) = some (.Ok 1#usize, middle, one lo))
    (second : readStep middle (one 0#u8) = some (.Ok 1#usize, after, one hi))
    (next : core.result.Result (Option U16) NativeIoError × NativeFile → NativeM α) :
    (read_word file >>= next).run (fileEnv env file before frame) =
      (next (.Ok (some (word lo hi)), file)).run (fileEnv env file after frame) := by
  simp only [read_word, NativeM.lift, monadLift_self, Result.ok_bind,
    bind_assoc, Array.to_slice_mut, Array.to_slice, Array.make_val]
  change (io_core.read_once file (one 0#u8) >>= _).run _ = _
  rw [read_next file (one 0#u8) env frame before middle _ (one lo)
    separate valid notBlocked first]
  simp only [UScalar.ofNat, UScalar.ofNatCore_val_eq, bind_assoc]
  change (io_core.read_once file (one 0#u8) >>= _).run _ = _
  rw [read_next file (one 0#u8) env frame middle after _ (one hi)
    separate validMiddle notBlockedMiddle second]
  simp [NativeM.ok, NativeM.lift, Array.from_slice, one, Array.index_usize,
    NativeM.monadLift_eq, NativeM.fromRust, word, Result.ok_bind]

/-- Both cross-crate word reads feed the actual internal integrity check. -/
theorem record_ready (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (s0 s1 s2 s3 s4 : State) (a b c d : U8)
    (separate : Separate file frame)
    (v0 : Valid s0) (v1 : Valid s1) (v2 : Valid s2) (v3 : Valid s3)
    (n0 : blocked s0 = false) (n1 : blocked s1 = false)
    (n2 : blocked s2 = false) (n3 : blocked s3 = false)
    (r0 : readStep s0 (one 0#u8) = some (.Ok 1#usize, s1, one a))
    (r1 : readStep s1 (one 0#u8) = some (.Ok 1#usize, s2, one b))
    (r2 : readStep s2 (one 0#u8) = some (.Ok 1#usize, s3, one c))
    (r3 : readStep s3 (one 0#u8) = some (.Ok 1#usize, s4, one d)) :
    (read_record file).run (fileEnv env file s0 frame) =
      (io_core.decode_record (word a b) (word c d) >>= fun value =>
        NativeM.ok (.Ok value, file)) (fileEnv env file s4 frame) := by
  simp only [read_record, monadLift_self]
  rw [word_next file env frame s0 s1 s2 a b separate v0 v1 n0 n1 r0 r1]
  rw [word_next file env frame s2 s3 s4 c d separate v2 v3 n2 n3 r2 r3]


/-- Actual cross-crate reads of a torn fresh slot either reject or return the
original input. Read steps and state validity remain the declared I/O boundary. -/
theorem record_torn (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (s0 s1 s2 s3 s4 : State)
    (value : U16) (a b c d : Bool)
    (separate : Separate file frame)
    (v0 : Valid s0) (v1 : Valid s1) (v2 : Valid s2) (v3 : Valid s3)
    (n0 : blocked s0 = false) (n1 : blocked s1 = false)
    (n2 : blocked s2 = false) (n3 : blocked s3 = false)
    (r0 : readStep s0 (one 0#u8) = some (.Ok 1#usize, s1, one (selected a (low value))))
    (r1 : readStep s1 (one 0#u8) = some (.Ok 1#usize, s2, one (selected b (high value))))
    (r2 : readStep s2 (one 0#u8) = some (.Ok 1#usize, s3, one (selected c (low (~~~value)))))
    (r3 : readStep s3 (one 0#u8) = some (.Ok 1#usize, s4, one (selected d (high (~~~value))))) :
    (read_record file).run (fileEnv env file s0 frame) =
      (.ok (.Ok none, file), fileEnv env file s4 frame) ∨
    (read_record file).run (fileEnv env file s0 frame) =
      (.ok (.Ok (some value), file), fileEnv env file s4 frame) := by
  rw [record_ready file env frame s0 s1 s2 s3 s4 _ _ _ _ separate
    v0 v1 v2 v3 n0 n1 n2 n3 r0 r1 r2 r3]
  rcases torn_decode value a b c d with rejected | accepted
  · left
    simp [rejected, NativeM.ok]
  · right
    simp [accepted, NativeM.ok]


@[expose] def rawByte (byte : U8) : UInt8 := UInt8.ofNat byte.val

@[simp] theorem raw_toNat (byte : U8) : (rawByte byte).toNat = byte.val := by
  simp [rawByte, Nat.mod_eq_of_lt (U8.lt_succ_max byte)]

@[simp] theorem restore_byte (byte : U8) (h : byte.val < 2^UScalarTy.U8.numBits) :
    U8.ofNatCore byte.val h = byte := by
  apply UScalar.eq_of_val_eq
  simp [U8.ofNatCore]

theorem byte_roundtrip (byte : U8) : byteValue (rawByte byte) = byte := by
  apply UScalar.eq_of_val_eq
  simp [byteValue, rawByte, U8.ofNatCore, Nat.mod_eq_of_lt (U8.lt_succ_max byte)]

@[expose] def fourBytes (a b c d : U8) : ByteArray :=
  ⟨#[rawByte a, rawByte b, rawByte c, rawByte d]⟩

@[expose] def readScript (mask : ByteArray) (rest : Term) : Nat → Term
  | 0 => rest
  | n + 1 => outcome "read" true 1 mask (readScript mask rest n)

@[expose] def reading (data : ByteArray) (rest : Term) (position : Nat) : State :=
  ⟨data, data, position, readScript (zeroMask data) rest (4 - position)⟩

/-- A concrete admissible sequence reads all four bytes; no parser postcondition
or assumed read transition is supplied by the client. -/
theorem four_reads (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (a b c d : U8) (rest : Term)
    (separate : Separate file frame) :
    (read_record file).run (fileEnv env file (reading (fourBytes a b c d) rest 0) frame) =
      (io_core.decode_record (word a b) (word c d) >>= fun value =>
        NativeM.ok (.Ok value, file))
          (fileEnv env file (reading (fourBytes a b c d) rest 4) frame) := by
  apply record_ready file env frame
    (reading (fourBytes a b c d) rest 0) (reading (fourBytes a b c d) rest 1)
    (reading (fourBytes a b c d) rest 2) (reading (fourBytes a b c d) rest 3)
    (reading (fourBytes a b c d) rest 4) a b c d separate
  all_goals simp [reading, fourBytes, Valid, limit, blocked, readScript,
    outcome, readStep, action, persist_zero, one, readBuffer, raw_toNat, restore_byte,
    Usize.ofNatCore, UScalar.ofNat, ← ByteArray.size_data]


/-- Actual seeking and reading compose, even when the incoming offset is at EOF. -/
theorem recover_four (file : NativeFile) (env : Environment)
    (frame : List (Nat × String × Term)) (a b c d : U8) (rest : Term) (position : Nat)
    (separate : Separate file frame) (bounded : position ≤ limit) :
    (recover_record file).run (fileEnv env file
      ⟨fourBytes a b c d, fourBytes a b c d, position,
        outcome "seek" true 0 (zeroMask (fourBytes a b c d))
          (readScript (zeroMask (fourBytes a b c d)) rest 4)⟩ frame) =
      (io_core.decode_record (word a b) (word c d) >>= fun value =>
        NativeM.ok (.Ok value, file))
          (fileEnv env file (reading (fourBytes a b c d) rest 4) frame) := by
  simp only [recover_record, monadLift_self]
  rw [seek_next file 0#u64 env frame _ (reading (fourBytes a b c d) rest 0)
    (.Ok 0#u64) separate]
  · exact four_reads file env frame a b c d rest separate
  · simpa [Valid, fourBytes, ← ByteArray.size_data, limit] using bounded
  · simp [blocked, outcome]
  · simpa [reading, sought] using seek_start
      (⟨fourBytes a b c d, fourBytes a b c d, position,
        outcome "seek" true 0 (zeroMask (fourBytes a b c d))
          (readScript (zeroMask (fourBytes a b c d)) rest 4)⟩ : State)
      0#u64 (zeroMask (fourBytes a b c d)) (fourBytes a b c d) _
      (by simp [limit]) (action_outcome _ _ _ _ _) (persist_zero _)

@[expose] def tornBytes (value : U16) (a b c d : Bool) : ByteArray :=
  fourBytes (selected a (low value)) (selected b (high value))
    (selected c (low (~~~value))) (selected d (high (~~~value)))

/-- Nonvacuous recovery of every complete zero/new torn fresh record: actual
seek, four reads and the internal check either reject or return the original. -/
theorem recover_torn_default (value : U16) (a b c d : Bool) (rest : Term) (highWater : Nat) :
    let image : Image := ⟨tornBytes value a b c d, highWater⟩
    let script := outcome "seek" true 0 (zeroMask image.bytes)
      (readScript (zeroMask image.bytes) rest 4)
    let file : NativeFile := ⟨highWater + 1⟩
    recover_record file (restarted image script) =
      (.ok (.Ok none, file), fileEnv ({} : Environment) file (reading image.bytes rest 4) []) ∨
    recover_record file (restarted image script) =
      (.ok (.Ok (some value), file), fileEnv ({} : Environment) file (reading image.bytes rest 4) []) := by
  dsimp only
  have equation := recover_four (⟨highWater + 1⟩ : NativeFile) ({} : Environment) []
    (selected a (low value)) (selected b (high value))
    (selected c (low (~~~value))) (selected d (high (~~~value))) rest 0
    (by simp [Separate]) (by simp [limit])
  simp only [restart_as_fileEnv, tornBytes]
  rw [equation]
  rcases torn_decode value a b c d with rejected | accepted
  · left
    simp [rejected, NativeM.ok]
  · right
    simp [accepted, NativeM.ok]

@[expose] def choiceMask (a b c d : Bool) : ByteArray :=
  ⟨#[if a then 1 else 0, if b then 1 else 0, if c then 1 else 0, if d then 1 else 0]⟩

/-- Every four-byte old/new choice is an admitted crash image of a fresh slot. -/
theorem fresh_image (value : U16) (a b c d : Bool) :
    persist ByteArray.empty (fourBytes (low value) (high value) (low (~~~value)) (high (~~~value)))
      (choiceMask a b c d) = some (tornBytes value a b c d) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp [persist, choiceMask, tornBytes, fourBytes, selected, rawByte,
      ← ByteArray.size_data, ByteArray.get]
  all_goals
    repeat' apply And.intro
    all_goals rfl


/-- Compose the actual write/sync implementation before a caller continuation. -/
theorem protocol_next (file : NativeFile) (data : Slice U8)
    (env : Environment) (frame : List (Nat × String × Term))
    (before middle after : State) (amount : Usize)
    (separate : Separate file frame) (initial : Valid before) (intermediate : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (writeReady : writeStep before data = some (.Ok amount, middle))
    (syncReady : syncStep middle = some (.Ok (), after))
    (next : core.result.Result Usize NativeIoError × NativeFile → NativeM α) :
    (write_then_sync file data >>= next).run (fileEnv env file before frame) =
      (next (.Ok amount, file)).run (fileEnv env file after frame) := by
  have first : pollWrite file data (fileEnv env file before frame) =
      some (.ok (.Ok amount, file), fileEnv env file middle frame) := by
    simp [-getHandle, pollWrite, no_shared_handle_at env file before frame separate,
      lookup_at env file before frame separate initial, notBlocked,
      writeReady, store_at env file before middle frame separate]
  have second : pollSync file (fileEnv env file middle frame) =
      some (.ok (.Ok ()), fileEnv env file after frame) := by
    simp [pollSync, lookup_at env file middle frame separate intermediate, notBlockedMiddle,
      syncReady, store_at env file middle after frame separate]
  rw [cross_contract]
  simp only [bind_assoc]
  unfold NativeFile.write
  rw [Result.wait_bind, Result.wait_ready_run _ _ _ _ _ first]
  simp only [Result.ok_bind, bind_assoc]
  unfold NativeFile.syncAll
  rw [Result.wait_bind, Result.wait_ready_run _ _ _ _ _ second]
  simp [Result.ok_bind]

/-- The actual facade acknowledges exactly a full record write followed by sync. -/
theorem write_record_ready (file : NativeFile) (value : U16)
    (env : Environment) (frame : List (Nat × String × Term))
    (before middle after : State) (amount : Usize)
    (separate : Separate file frame) (initial : Valid before) (intermediate : Valid middle)
    (notBlocked : blocked before = false) (notBlockedMiddle : blocked middle = false)
    (writeReady : writeStep before (.from (layout value).val (by simp [layout]; scalar_tac)) =
      some (.Ok amount, middle))
    (syncReady : syncStep middle = some (.Ok (), after)) :
    write_record file value (fileEnv env file before frame) =
      (.ok (.Ok (decide (amount.val = 4)), file), fileEnv env file after frame) := by
  simp only [write_record, monadLift_self, encode_spec, NativeM.ok, Result.ok_bind,
    NativeM.lift, Array.to_slice]
  rw [protocol_next file _ env frame before middle after amount separate initial intermediate
    notBlocked notBlockedMiddle writeReady syncReady]
  dsimp only
  split <;> simp_all [NativeM.ok]

/-- The intact encoded record is always accepted with its original value. -/
theorem decode_layout (value : U16) :
    io_core.decode_record (word (low value) (high value))
      (word (low (~~~value)) (high (~~~value))) = NativeM.ok (some value) := by
  have identity (v : U16) : word (low v) (high v) = v := by
    apply U16.bv_eq_imp_eq
    simp only [word_bv, low, high]
    bv_normalize
  rw [identity, identity, decode_spec]
  have valid : value ^^^ (~~~value) = core.num.U16.MAX := by
    apply U16.bv_eq_imp_eq
    simp only [UScalar.bv_xor, UScalar.bv_not, core.num.U16.MAX,
      UScalar.ofNat, UScalar.ofNatCore_bv, U16.rMax, UScalarTy.numBits]
    change value.bv ^^^ ~~~value.bv = ~~~(0#16)
    rw [← BitVec.not_xor_right, BitVec.xor_self]
  simp only [valid, ite_true]

end Record.IntegrityProperties
