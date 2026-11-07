module
public import FileResource.Extraction.Funs
public import FileResource.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace FileResource.Creation
open NativeFile
@[expose] def path : ByteArray := ⟨#[114,101,115,111,117,114,99,101]⟩
@[expose] def choice (script : Term) : Term :=
  .cons (.tuple #[.atom "create_new",.bitstring path 0,.atom "ok",.integer 0,script]) .nil
@[expose] def initial (env : Environment) (script : Term) : Environment :=
  {env with refCounter := 0, nativeHeap := [(0,namespaceTypeName,encodeNamespace ⟨[],[],[],choice script⟩)]}
@[expose] def created (env : Environment) (script : Term) : Environment :=
  {env with refCounter := 2, nativeHeap := [
    (2,writableHandleTypeName,encodeHandle ⟨1,0,script⟩),
    (1,inodeTypeName,encode ⟨ByteArray.empty,ByteArray.empty,0,.nil⟩),
    (0,namespaceTypeName,encodeNamespace ⟨[(path,1)],[],[[(path,1)]],.nil⟩)]}
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem create_poll (env : Environment) (script : Term) :
    pollCreateNew (toStr "resource") (initial env script) =
      some (.ok (.Ok ⟨2⟩), created env script) := by
  have converted : bytes (toStr "resource") = path := by
    simp [bytes,toStr,Slice.from,Slice.val,Data.ListN.ListN.from_to_inverse,path]
    all_goals decide +kernel
  have supported : supportedPath path = true := by
    unfold path supportedPath
    decide +kernel
  simp [pollCreateNew,converted,supported,initial,created,choice,namespaceSnapshot,
    namespaceTable,namespaceHistory,encodeNamespace,encodeNames,tablesEqual,
    pathChoice,storeNamespace]

@[expose] def payload : effects_native.FileResource := ⟨⟨2⟩⟩
@[expose] def returned (env : Environment) (script : Term) : Environment :=
  {env with refCounter := 6, nativeHeap := NativeResourceArc.vmCells payload 3 5 6 ++ (created env script).nativeHeap}

theorem created_frame (env : Environment) (script : Term) :
    NativeResourceArc.FrameBelow effects_native.FileResource 2 (created env script).nativeHeap := by
  intro cell member
  simp only [created,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl <;>
    simp [NativeResourceArc.handleType,NativeResourceArc.termType,
      NativeCodec.typeName,writableHandleTypeName,
      inodeTypeName,namespaceTypeName]

/-- The actual extracted constructor performs exclusive creation before allocating the resource. -/
theorem constructor_prefix (env : Environment) (script : Term) :
    Result.ReadyPrefix
      __CREATE__
      (initial env script) (NativeResourceArc.newOwned payload) (created env script) := by
  simp only [__CREATE__,
    monadLift_self,NativeFile.createNew,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ (.ok (.Ok ⟨2⟩)) _ _ _ _ (create_poll env script)
  simpa [NativeM.expectOk,NativeM.ok,effects_native.file_resource_new,payload] using
    Result.ReadyPrefix.refl (NativeResourceArc.newOwned payload) (created env script)

/-- The compiled Rustler return path installs a VM pin and consumes its temporary Rust owner. -/
theorem create_next {α : Type} (env : Environment) (script : Term) (next : Term → Result α)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (Rustler.executeNative (do
      let value ← __CREATE__
      let term ← NativeResourceArc.encode value
      NativeOwnedDrop.drop value
      Result.ok term) id >>= next) (initial env script) =
      next (.reference 6) (returned env script) := by
  have trace := Rustler.executeNative_readyPrefix ((constructor_prefix env script).bind
    (fun value => do
      let term ← NativeResourceArc.encode value
      NativeOwnedDrop.drop value
      Result.ok term)) id
  rw [(trace.bind next).apply]
  simp only [Rustler.executeNative,bind_assoc,Result.ok_bind,id_eq,
    NativeOwnedDrop.drop]
  simpa [returned,created] using
    NativeResourceArc.newOwned_encode_release_framed_next payload _ next
      (created env script) registered (created_frame env script)

/-- Apply the constructor contract in the caller's current runtime environment. -/
theorem create_env {α : Type} (script : Term) (next : Term → Result α) (env : Environment)
    (counter : env.refCounter = 0)
    (heap : env.nativeHeap = (initial env script).nativeHeap)
    (registered : NativeResourceArc.typeName effects_native.FileResource ∈ env.nativeResourceTypes) :
    (Rustler.executeNative (do
      let value ← __CREATE__
      let term ← NativeResourceArc.encode value
      NativeOwnedDrop.drop value
      Result.ok term) id >>= next) env = next (.reference 6) (returned env script) := by
  have same : initial env script = env := by
    cases env
    simp_all [initial]
  simpa only [same] using create_next env script next registered

/-- The filesystem is admitted, but no resource or file handle exists initially. -/
@[expose] def seed : Environment := initial {} .nil
end FileResource.Creation
