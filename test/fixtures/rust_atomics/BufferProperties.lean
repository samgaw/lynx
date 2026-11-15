module
public import Buffer.Extraction.Funs
public import Buffer.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Buffer.Properties
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

theorem standard_get_total (bytes : Slice U8) (index : Usize) :
    ∃ result, core.slice.index.Usize.get index bytes = RustM.ok result := ⟨_, rfl⟩

theorem core_length (bytes : Slice U8) :
    atomic_core.buffer_length bytes = NativeM.ok (Slice.len bytes) := rfl

theorem length_composition (bytes : Slice U8) :
    atomic_analysis.buffer_length bytes = NativeM.ok (Slice.len bytes) := rfl

theorem core_head (bytes : Slice U8) :
    atomic_core.buffer_head bytes = NativeM.ok (bytes.val.headD 0#u8) := by
  cases contents : bytes.val <;>
    simp [atomic_core.buffer_head, core.slice.Slice.get, core.slice.index.SliceIndexUsizeSlice,
      core.slice.index.Usize.get, NativeM.lift, NativeM.ok, contents]

theorem head_composition (bytes : Slice U8) :
    atomic_analysis.buffer_head bytes = NativeM.ok (bytes.val.headD 0#u8) := by
  simp [atomic_analysis.buffer_head, core_head]

theorem cleanup (payload : ByteBuffer) :
    ByteBuffer.drop_owned payload = NativeM.ok () := rfl

theorem dispose (handle : NativeResourceArc ByteBuffer) :
    buffer_dispose handle = NativeResourceArc.releaseOwned handle := rfl

@[expose] def payload (first second : U8) : ByteBuffer :=
  ⟨alloc.vec.Vec.from [first, second] (by scalar_tac)⟩

theorem create (first second : U8) :
    __NEW__ first second = NativeResourceArc.newOwned (payload first second) := by
  simp [__NEW__, Buffer.Extraction.VectorModel.push_eq,
    NativeM.lift, NativeM.ok, alloc.vec.Vec.new, payload]

theorem read_length (handle : NativeResourceArc ByteBuffer) :
    __LENGTH__ handle = (do
      let value ← NativeResourceArc.deref handle
      let length ← NativeM.lift (UScalar.cast .U64 (Slice.len (alloc.vec.Vec.deref value.bytes)))
      NativeResourceArc.releaseOwned handle
      NativeM.ok length) := by
  simp [__LENGTH__, length_composition, NativeOwnedDrop.drop, NativeM.ok]

theorem read_head (handle : NativeResourceArc ByteBuffer) :
    __HEAD__ handle = (do
      let value ← NativeResourceArc.deref handle
      NativeResourceArc.releaseOwned handle
      NativeM.ok (value.bytes.val.headD 0#u8)) := by
  simp [__HEAD__, head_composition, NativeOwnedDrop.drop, NativeM.ok, alloc.vec.Vec.deref]

@[expose] def live (env : Environment) (value : ByteBuffer) : Environment :=
  {env with nativeRefCounter := 2, nativeHeap := [
    (2, NativeResourceArc.handleType ByteBuffer, .nativeReference 1),
    (1, NativeResourceArc.typeName ByteBuffer, .tuple #[.integer 1, NativeCodec.encode value])]}

/-- Final callback execution requires an explicit policy; no VM scheduling
assumption is inserted into the implementation or its ordinary Elixir laws. -/
theorem final_release (value : ByteBuffer) (env : Environment)
    (policy : env.nativeFinalizerMode = .synchronous) :
    buffer_dispose ⟨1, 2⟩ (live env value) =
      (.ok (), {env with nativeRefCounter := 2, nativeHeap := []}) := by
  have released := NativeResourceArc.releaseOwned_last_run_next
    (⟨1, 2⟩ : NativeResourceArc ByteBuffer) value NativeM.ok (live env value)
    {env with nativeRefCounter := 2, nativeHeap := []}
    (.inr (by simpa [live] using policy))
    (by simp [live]) (by simp [live])
    (by simp [live, NativeResourceArc.handleType, NativeResourceArc.typeName])
    (by intro next; simp [NativeResourceCleanup.cleanup, ByteBuffer.drop_owned,
      NativeResourceArc.retiredState, live, NativeM.ok])
  have identity : (NativeResourceArc.releaseOwned (⟨1, 2⟩ : NativeResourceArc ByteBuffer) >>= NativeM.ok) =
      NativeResourceArc.releaseOwned (⟨1, 2⟩ : NativeResourceArc ByteBuffer) := Result.bind_ok _
  rw [identity] at released
  simpa [dispose, NativeM.ok] using released

theorem invalid_byte :
    NativeCodec.decode (α := alloc.vec.Vec U8) (Term.list [.integer 256]) = none := by cbv

theorem improper_bytes :
    NativeCodec.decode (α := alloc.vec.Vec U8) (.cons (.integer 1) (.integer 2)) = none := by cbv

end Buffer.Properties
