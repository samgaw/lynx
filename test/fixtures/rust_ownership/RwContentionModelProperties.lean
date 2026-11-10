module
public import RwShared.NativeRuntime
public section
open Aeneas Aeneas.Std Lynx
namespace RwShared.ContentionModel

@[expose] def held (value : Bool) : Environment :=
  {currentPid := [1], nativeRefCounter := 2, nativeHeap :=
    [(1, NativeRwLock.typeName Bool,
      NativeRwLock.contents (⟨[],some (2,[]),false,value⟩ : NativeRwLock.State Bool))]}

@[expose] def queued (value : Bool) : Environment :=
  {held value with nativeRefCounter := 3, nativeHeap :=
    (3, NativeRwLock.writerRequestType (⟨1⟩ : NativeRwLock Bool),
      .tuple #[.nativeReference 1,.pid [1]]) :: (held value).nativeHeap}

/-- Writer registration is a transition, not a successful acquisition. -/
theorem registers (value : Bool) :
    NativeRwLock.pollWrite (⟨1⟩ : NativeRwLock Bool) (held value) =
      some (.waiting 3, queued value) := by
  cases value <;> cbv

/-- Both an initial reader and a queued writer remain blocked by another writer. -/
theorem waits (value : Bool) :
    NativeRwLock.pollRead (⟨1⟩ : NativeRwLock Bool) (held value) = none ∧
      NativeRwLock.pollWaitingWrite (⟨1⟩ : NativeRwLock Bool) 3 (queued value) = none := by
  cases value <;> cbv

/-- Do not assume that an OS permits a new reader to pass a waiting writer. -/
theorem reader_priority_unsupported (value : Bool) :
    NativeRwLock.pollRead (⟨1⟩ : NativeRwLock Bool) (queued value) =
      some (.error .exhausted, queued value) := by
  cases value <;> cbv

/-- A pending request cannot be presented in another execution context. -/
theorem wrong_context (value : Bool) :
    let env := {queued value with currentPid := []}
    NativeRwLock.pollWaitingWrite (⟨1⟩ : NativeRwLock Bool) 3 env =
      some (.error .exhausted,env) := by
  cases value <;> cbv

/-- A ticket for one lock does not authorize acquiring another lock. -/
theorem wrong_lock (value : Bool) :
    NativeRwLock.pollWaitingWrite (⟨2⟩ : NativeRwLock Bool) 3 (queued value) =
      some (.error .exhausted,queued value) := by
  cases value <;> cbv

@[expose] def released (value : Bool) : Environment :=
  {currentPid := [1], nativeRefCounter := 5, nativeHeap :=
    [(3, NativeRwLock.writerRequestType (⟨1⟩ : NativeRwLock Bool),
        .tuple #[.nativeReference 1,.pid [1]]),
      (5, NativeRwLock.writerRequestType (⟨1⟩ : NativeRwLock Bool),
        .tuple #[.nativeReference 1,.pid [2]]),
      (1, NativeRwLock.typeName Bool,
        NativeRwLock.contents (⟨[],none,false,value⟩ : NativeRwLock.State Bool))]}

/-- Resumption retires only the acquired request and keeps a peer queued. -/
theorem resumes_preserves_peer (value : Bool) :
    NativeRwLock.pollWaitingWrite (⟨1⟩ : NativeRwLock Bool) 3 (released value) =
      some (.ok (.Ok ⟨⟨1⟩,6,[1],value⟩),
        {currentPid := [1], nativeRefCounter := 6, nativeHeap :=
          [(5, NativeRwLock.writerRequestType (⟨1⟩ : NativeRwLock Bool),
              .tuple #[.nativeReference 1,.pid [2]]),
            (1, NativeRwLock.typeName Bool,
              NativeRwLock.contents (⟨[],some (6,[1]),false,value⟩ : NativeRwLock.State Bool))]}) := by
  cases value <;> cbv

/-- A free lease is insufficient to dispose a lock with pending owners. -/
theorem pending_prevents_disposal (value : Bool) :
    (NativeRwLock.dispose (⟨1⟩ : NativeRwLock Bool)).run (released value) [] =
      (.error .exhausted,released value) := by
  cases value <;>
    simp [NativeRwLock.dispose, released, NativeRwLock.writerWaiting,
      NativeRwLock.writerRequestType, NativeRwLock.state, NativeRwLock.decodeState,
      NativeRwLock.contents, NativeRwLock.decodeLease, NativeRwLock.readerLimit,
      NativeRwLock.typeName, NativeCodec.decode, NativeCodec.encode]

end RwShared.ContentionModel
