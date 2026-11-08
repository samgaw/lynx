module
public import Resource.NativeRuntime
public section
open Lynx

namespace Resource.ModelProperties

/-- Model theorem only: extracted ResourceArc admission is checked separately. -/
theorem retained_payload (value : Bool) (env : Environment)
    (registered : NativeResourceArc.typeName Bool ∈ env.nativeResourceTypes)
    (empty : env.nativeHeap = []) :
    (do
      let first ← NativeResourceArc.new value
      let retained ← NativeResourceArc.clone first
      NativeResourceArc.release first
      let observed ← NativeResourceArc.deref retained
      NativeResourceArc.release retained
      Result.ok observed) env =
        (.ok value, { env with refCounter := env.refCounter + 3 }) := by
  exact NativeResourceArc.clone_release_cycle value env registered empty

theorem absent_registration (value : Bool) (env : Environment)
    (absent : NativeResourceArc.typeName Bool ∉ env.nativeResourceTypes) :
    NativeResourceArc.new value env = (.error (.error (.atom "rust_panicked")), env) := by
  exact NativeResourceArc.new_unregistered value env absent

theorem consumed_release (handle : NativeResourceArc Bool) (env : Environment)
    (absent : env.nativeHeap.filter (fun cell => cell.1 == handle.token) = []) :
    NativeResourceArc.release handle env = (.error .exhausted, env) := by
  exact NativeResourceArc.release_missing handle env absent

theorem forged_count (handle : NativeResourceArc Bool) (value : Bool) (env : Environment)
    (distinct : handle.id ≠ handle.token)
    (stored : env.nativeHeap = [
      (handle.token, NativeResourceArc.handleType Bool, .reference handle.id),
      (handle.id, NativeResourceArc.typeName Bool,
        .tuple #[.integer 2, NativeCodec.encode value])]) :
    NativeResourceArc.deref handle env = (.error .exhausted, env) := by
  exact NativeResourceArc.deref_inconsistent_count handle value env distinct stored

/-- Identity freshness alone cannot justify allocation if an older token points
at the prospective new allocation. The resource frame must exclude this alias. -/
theorem future_owner_not_bounded :
    ¬ NativeResourceArc.FrameBelow Bool 1 [(1, NativeResourceArc.handleType Bool, .reference 2)] := by
  intro bounded
  have impossible := (bounded (1, NativeResourceArc.handleType Bool, .reference 2)
    (by simp)).2.1 rfl 2 rfl
  omega

/-- Ordinary imports expose the actual retained-borrow prefix without exposing lookup internals. -/
theorem retained_borrow_prefix (handle : NativeResourceArc Bool) (value : Bool) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token,NativeResourceArc.handleType Bool,.reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id,NativeResourceArc.typeName Bool,.tuple #[.integer 2,NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType Bool && cell.2.2 == .reference handle.id).length = 2) :
    Result.ReadyPrefix (NativeResourceArc.deref handle) env (.ok value) env := by
  exact NativeResourceArc.deref_retained_prefix handle value env token stored owners

/-- Generated runtime clients can retain the decoder's actual registry/clone steps. -/
theorem pinned_decode_prefix (value : Bool) (env : Environment) (id pin term : Nat)
    (pinned : NativeResourceArc.Pinned value id pin term env)
    (registered : NativeResourceArc.typeName Bool ∈ env.nativeResourceTypes) :
    Result.ReadyPrefix (NativeResourceArc.decode (.reference term)) env
      (.ok (⟨id,env.refCounter + 1⟩ : NativeResourceArc Bool)) {env with
        refCounter := env.refCounter + 1
        nativeHeap := (env.refCounter + 1,NativeResourceArc.handleType Bool,.reference id) ::
          env.nativeHeap.map fun cell => if cell.1 == id then
            (id,NativeResourceArc.typeName Bool,.tuple #[.integer 2,NativeCodec.encode value]) else cell} := by
  exact NativeResourceArc.decode_pinned_prefix value env id pin term pinned registered

/-- Nonfinal owned release retains its actual state transitions and payload. -/
theorem retained_release_prefix [NativeResourceCleanup Bool] (handle : NativeResourceArc Bool) (value : Bool) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token,NativeResourceArc.handleType Bool,.reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id,NativeResourceArc.typeName Bool,.tuple #[.integer 2,NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType Bool && cell.2.2 == .reference handle.id).length = 2) :
    Result.ReadyPrefix (NativeResourceArc.releaseOwned handle) env (.ok ()) ({env with
      nativeHeap := List.map (fun cell => if cell.1 == handle.id then
        (handle.id,NativeResourceArc.typeName Bool,.tuple #[.integer 1,NativeCodec.encode value]) else cell)
        (List.filter (fun cell => cell.1 != handle.token) env.nativeHeap)}) := by
  exact NativeResourceArc.releaseOwned_retained_prefix handle value env token stored owners

/-- Two Rust callers can borrow alongside a surviving VM pin. The public
interface retains the read boundary and checks all three ownership tokens. -/
theorem overlapping_borrow_prefix (handle : NativeResourceArc Bool) (value : Bool) (env : Environment)
    (token : env.nativeHeap.filter (fun cell => cell.1 == handle.token) =
      [(handle.token, NativeResourceArc.handleType Bool, .reference handle.id)])
    (stored : env.nativeHeap.filter (fun cell => cell.1 == handle.id) =
      [(handle.id, NativeResourceArc.typeName Bool, .tuple #[.integer 3, NativeCodec.encode value])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType Bool && cell.2.2 == .reference handle.id).length = 3) :
    Result.ReadyPrefix (NativeResourceArc.deref handle) env (.ok value) env := by
  exact NativeResourceArc.deref_live_prefix handle value 3 env (by decide) (by decide)
    token stored owners

end Resource.ModelProperties
