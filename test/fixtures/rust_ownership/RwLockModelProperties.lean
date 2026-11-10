module
public import Rw.NativeRuntime
public section
open Aeneas Aeneas.Std Lynx
namespace Rw.ModelProperties

@[expose] def readers (value : Bool) : Environment :=
  {nativeRefCounter := 3, nativeHeap :=
    [(1, NativeRwLock.typeName Bool,
      NativeRwLock.contents (⟨[(2,[]),(3,[])],none,false,value⟩ : NativeRwLock.State Bool))]}

@[expose] def writer (value : Bool) : Environment :=
  {nativeRefCounter := 2, nativeHeap :=
    [(1, NativeRwLock.typeName Bool,
      NativeRwLock.contents (⟨[],some (2,[]),false,value⟩ : NativeRwLock.State Bool))]}

/-- A conflict cannot manufacture an acquisition or a catchable Rust error. -/
theorem writer_conflicts_with_readers (value : Bool) :
    NativeRwLock.acquireWrite (⟨1⟩ : NativeRwLock Bool) (readers value) =
      (.error .exhausted, readers value) := by
  cases value <;> simp [NativeRwLock.acquireWrite, NativeRwLock.state, readers,
    NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
    NativeRwLock.lease, NativeRwLock.readerLimit, List.eraseDups_cons, List.eraseDups_nil,
    NativeCodec.encode, NativeCodec.decode]

theorem reader_conflicts_with_writer (value : Bool) :
    NativeRwLock.acquireRead (⟨1⟩ : NativeRwLock Bool) (writer value) =
      (.error .exhausted, writer value) := by
  cases value <;> simp [NativeRwLock.acquireRead, NativeRwLock.state, writer,
    NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
    NativeRwLock.lease, NativeRwLock.readerLimit, List.eraseDups_nil,
    NativeCodec.encode, NativeCodec.decode]

/-- Reader cleanup keeps the other lease and never poisons the lock. -/
theorem read_unwind (value : Bool) :
    NativeUnwindDrop.drop (⟨⟨1⟩,2,[],value⟩ : NativeRwReadGuard Bool) (readers value) =
      (.ok (), {nativeRefCounter := 3, nativeHeap :=
        [(1, NativeRwLock.typeName Bool,
          NativeRwLock.contents (⟨[(3,[])],none,false,value⟩ : NativeRwLock.State Bool))]}) := by
  cases value <;> simp [NativeUnwindDrop.drop, NativeRwLock.releaseRead,
    NativeRwLock.state, NativeRwLock.store, readers,
    NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
    NativeRwLock.lease, NativeRwLock.readerLimit, List.eraseDups_cons, List.eraseDups_nil,
    NativeCodec.encode, NativeCodec.decode, Result.ofExcept]

/-- Writer cleanup commits the current borrowed value before setting poison. -/
theorem write_unwind (value : Bool) :
    NativeUnwindDrop.drop (⟨⟨1⟩,2,[],!value⟩ : NativeRwWriteGuard Bool) (writer value) =
      (.ok (), {nativeRefCounter := 2, nativeHeap :=
        [(1, NativeRwLock.typeName Bool,
          NativeRwLock.contents (⟨[],none,true,!value⟩ : NativeRwLock.State Bool))]}) := by
  cases value <;> simp [NativeUnwindDrop.drop, NativeRwLock.releaseWrite,
    NativeRwLock.state, NativeRwLock.store, writer,
    NativeRwLock.contents, NativeRwLock.decodeState, NativeRwLock.decodeLease,
    NativeRwLock.lease, NativeRwLock.readerLimit, List.eraseDups_nil,
    NativeCodec.encode, NativeCodec.decode, Result.ofExcept]
end Rw.ModelProperties
