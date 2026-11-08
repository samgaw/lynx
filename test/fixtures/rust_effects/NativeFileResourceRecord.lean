module
public import FileResource.Recovery
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Record
open NativeFile FileResource.Creation FileResource.CreatedCalls

@[expose] def word (low high : U8) : U16 :=
  core.num.U16.from_le_bytes (Array.make 2#usize [low,high])

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
theorem encode_spec (value : U16) : effects_core.encode_record value = NativeM.ok (layout value) := by
  simp [effects_core.encode_record, NativeM.lift, NativeM.ok, Array.index_usize,
    core.num.U16.to_le_bytes, BitVec.toLEBytes, NativeM.monadLift_eq, NativeM.fromRust,
    layout, low, high, ]

/-- This equation is derived from the actual Rust check, not an assumed decoder. -/
theorem decode_spec (value inverse : U16) :
    effects_core.decode_record value inverse = NativeM.ok
      (if value ^^^ inverse = core.num.U16.MAX then some value else none) := by
  by_cases h : value ^^^ inverse = core.num.U16.MAX <;>
    simp [effects_core.decode_record, NativeM.lift, NativeM.ok, h]

@[expose] def selected (persisted : Bool) (byte : U8) : U8 := if persisted then byte else 0#u8

private theorem ones_bit (i : Nat) (h : i < 16) : (65535#16).getLsbD i = true := by
  interval_cases i <;> decide

/-- In a fresh record slot, zero/new byte tearing cannot produce a different
accepted value, including the degenerate all-zero and all-one input bytes. -/
theorem torn_decode (value : U16) (a b c d : Bool) :
    effects_core.decode_record (word (selected a (low value)) (selected b (high value)))
      (word (selected c (low (~~~value))) (selected d (high (~~~value)))) = NativeM.ok none ∨
    effects_core.decode_record (word (selected a (low value)) (selected b (high value)))
      (word (selected c (low (~~~value))) (selected d (high (~~~value)))) = NativeM.ok (some value) := by
  simp only [decode_spec]
  split
  · rename_i valid
    right
    have bits := congrArg UScalar.bv valid
    have equal : (word (selected a (low value)) (selected b (high value))).bv = value.bv := by
      cases a <;> cases b <;> cases c <;> cases d
      all_goals
        simp only [selected, Bool.false_eq_true, ite_false, ite_true, word_bv,
          low, high, UScalar.bv_xor, UScalar.bv_not, core.num.U16.MAX,
          UScalar.ofNat, UScalar.ofNatCore_bv, U16.rMax, UScalarTy.numBits] at bits ⊢
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        have bit := congrArg (fun (x : BitVec 16) => x.getLsbD i) bits
        rw [ones_bit i hi] at bit
        interval_cases i <;>
          simp only [BitVec.getLsbD_xor, BitVec.getLsbD_append,
              BitVec.getLsbD_ofNat] at bit ⊢ <;>
          simp_all
    have same : word (selected a (low value)) (selected b (high value)) = value := by
      apply UScalar.eq_of_val_eq
      exact congrArg BitVec.toNat equal
    rw [same]
  · left
    rfl



@[expose] def wire (value : U16) : Slice U8 := Array.to_slice (layout value)
@[expose] def content (value : U16) : ByteArray := bytes (wire value)

theorem wire_length (value : U16) : (wire value).val.length = 4 := by
  simp [wire,layout]

theorem content_size (value : U16) : (content value).size = 4 := by
  simpa [content,bytes,← ByteArray.size_data] using wire_length value


/-- The actual facade reports complete versus partial writes while retaining its VM-held file. -/
theorem write_next {ns : NamespaceSnapshot} {α : Type} (env : Environment) (before after : State) (counter : Nat)
    (bounded : 6 ≤ counter) (valid : Valid before) (ready : blocked before = false)
    (value : U16) (count : Usize)
    (step : writeStep before (wire value) = some (.Ok count,after))
    (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool
      next result) (pinnedEnv env before counter ns) =
    next (Rustler.encodeBool (count = 4#usize)) (pinnedEnv env after (counter + 1) ns) := by
  have trace : Result.ReadyPrefix (effects_core.write_shared_file payload.file (wire value))
      (decodedEnv env before counter ns) (.ok (.Ok count)) (decodedEnv env after counter ns) := by
    simp only [effects_core.write_shared_file,monadLift_self,write,Result.wait_bind,payload]
    apply Result.ReadyPrefix.wait _ _ (.ok (.Ok count,⟨2⟩)) _ _ _ _
      (write_poll (ns := ns) env before after counter bounded valid (wire value) ready (.Ok count) step)
    simpa [NativeM.ok] using Result.ReadyPrefix.refl
      (Result.ok (.Ok count : core.result.Result Usize NativeIoError)) (decodedEnv env after counter ns)
  let finish := fun outcome : core.result.Result Usize NativeIoError => do
    let result : Bool ← match outcome with
      | .Ok written => NativeM.ok (written = 4#usize)
      | .Err error => do NativeOwnedDrop.drop error; NativeM.ok false
    Result.ok (Rustler.encodeBool result)
  let handler : Exception → Result Term := fun error => match error with
    | .error (.atom "rust_panicked") => Result.error (.error (.atom "nif_panicked"))
    | _ => Result.error .exhausted
  have result := retained_effect_next (ns := ns) env before after counter bounded
    (fun resource => effects_core.write_shared_file resource.file (wire value))
    (.Ok count) finish handler next registered trace
  have compiled (owner : NativeResourceArc effects_native.FileResource) :
      (do let result ← __WRITE_RECORD__ owner value; Result.ok (Rustler.encodeBool result)) =
      (do
        let resource ← NativeResourceArc.deref owner
        let outcome ← effects_core.write_shared_file resource.file (wire value)
        NativeResourceArc.releaseOwned owner
        finish outcome) := by
    simp only [__WRITE_RECORD__,file_resource_write_record,encode_spec,file_resource_release,
      monadLift_self,NativeM.lift,NativeM.ok,Result.ok_bind,wire,bind_assoc,NativeOwnedDrop.drop]
    congr 1
    funext resource
    congr 1
    funext outcome
    congr 1
    funext ignored
    cases outcome <;> simp [finish,NativeM.ok,NativeOwnedDrop.drop,bind_assoc]
  simp only [Rustler.executeNative,compiled]
  convert result using 1 <;> simp [finish,handler,NativeM.ok,Result.handle]
  all_goals rfl


/-- The verified write contract applies in an ordinary caller's current environment. -/
theorem write_env {ns : NamespaceSnapshot} {α : Type} (before after : State) (valid : Valid before)
    (ready : blocked before = false) (value : U16) (count : Usize)
    (step : writeStep before (wire value) = some (.Ok count,after)) (next : Term → Result α)
    (env : Environment) (bounded : 6 ≤ env.nativeRefCounter)
    (heap : env.nativeHeap = NativeResourceArc.vmCells payload 3 5 6 ++ frame before ns)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      let result ← Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool
      next result) env = next (Rustler.encodeBool (count = 4#usize))
        (pinnedEnv env after (env.nativeRefCounter + 1) ns) := by
  simpa only [pinnedEnv,← heap] using
    write_next (ns := ns) env before after env.nativeRefCounter bounded valid ready value count step next registered

@[expose] def writeChoice (count : Nat) : Term :=
  .cons (.tuple #[.atom "write",.atom "ok",.integer count,.bitstring ByteArray.empty 0]) (syncChoice .nil)
@[expose] def before : State := ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 4⟩
@[expose] def written (value : U16) : State := ⟨content value,ByteArray.empty,4,syncChoice .nil⟩
@[expose] def synced (value : U16) : State := ⟨content value,content value,4,.nil⟩
@[expose] def seed : Environment := initial {} before.script

theorem before_valid : Valid before := by simp [Valid,before,limit,← ByteArray.size_data]
theorem written_valid (value : U16) : Valid (written value) := by
  simp only [Valid,written,content_size]
  simp [limit,← ByteArray.size_data]
theorem before_ready : blocked before = false := rfl
theorem written_ready (value : U16) : blocked (written value) = false := rfl

theorem full_step (value : U16) : writeStep before (wire value) = some (.Ok 4#usize,written value) := by
  have take : (bytes (wire value)).data.toList.take 4 = (bytes (wire value)).data.toList := by
    apply List.take_of_length_le
    have size : (bytes (wire value)).data.toList.length = 4 := by
      simpa [content,← ByteArray.size_data] using content_size value
    omega
  simp [writeStep,before,written,writeChoice,action,wire_length,limit,
    overwrite,persist,take,content,← ByteArray.size_data]
  constructor
  · apply UScalar.eq_of_val_eq; rfl
  · rfl

theorem sync_step (value : U16) : syncStep (written value) = some (.Ok (),synced value) := by
  simp [syncStep,written,synced,syncChoice,action]


/-- The intact encoded record is always accepted with its original value. -/
theorem decode_layout (value : U16) :
    effects_core.decode_record (word (low value) (high value))
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

@[expose] def recordSeed : Environment := initial {} before.script Publish.opening
@[expose] def done (env : Environment) (value : U16) : Environment :=
  Publish.committedEnv env (synced value) 7

theorem returned_before (env : Environment) :
    returned env before.script Publish.opening = pinnedEnv env before 6 Publish.namespaceBefore := rfl

/-- Actual resource creation, checked-record writing and durable name commitment compose. -/
theorem create_write_commit (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      let _ ← Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__COMMIT__ owner) Rustler.encodeBool) (initial env before.script Publish.opening) =
      (.ok Term.true,done env value) := by
  rw [create_next (rest := Publish.opening) env before.script _ registered,returned_before]
  rw [write_next (ns := Publish.namespaceBefore) env before (written value) 6 (by omega)
    before_valid before_ready value 4#usize (full_step value) _ registered]
  simpa [Result.bind_ok,Result.ok_apply,Rustler.encodeBool,done] using
    Publish.commit_next_state env (written value) (synced value) 7 (by omega)
      (written_valid value) (written_ready value) (sync_step value) Result.ok registered

@[expose] def partialBefore : State := ⟨ByteArray.empty,ByteArray.empty,0,writeChoice 1⟩
@[expose] def partialWritten (value : U16) : State :=
  ⟨overwrite ByteArray.empty 0 (content value) 1,ByteArray.empty,1,syncChoice .nil⟩

theorem partial_step (value : U16) :
    writeStep partialBefore (wire value) = some (.Ok 1#usize,partialWritten value) := by
  simp [writeStep,partialBefore,partialWritten,writeChoice,action,wire_length,
    limit,persist,content,← ByteArray.size_data]
  constructor
  · apply UScalar.eq_of_val_eq; rfl
  · rfl

/-- A real short write changes visible file state but is never acknowledged as complete. -/
theorem short_not_acknowledged (env : Environment) (value : U16)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (do
      let term ← Rustler.executeNative (do
        let value ← __CREATE__
        let term ← NativeResourceArc.encode value
        NativeOwnedDrop.drop value
        Result.ok term) id
      let owner ← NativeResourceArc.decode term
      Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool) (initial env partialBefore.script) =
      (.ok Term.false,pinnedEnv env (partialWritten value) 7) := by
  rw [create_next (rest := .nil) env partialBefore.script _ registered]
  change (do
      let owner ← NativeResourceArc.decode (.nativeReference 6)
      Rustler.executeNative (__WRITE_RECORD__ owner value) Rustler.encodeBool)
    (pinnedEnv env partialBefore 6) = _
  have valid : Valid partialBefore := by simp [Valid,partialBefore,limit,← ByteArray.size_data]
  simpa [Result.bind_ok,Result.ok_apply,Rustler.encodeBool] using
    write_next (ns := pendingNamespace) env partialBefore (partialWritten value) 6 (by omega) valid rfl value 1#usize
      (partial_step value) Result.ok registered

end FileResource.Record
