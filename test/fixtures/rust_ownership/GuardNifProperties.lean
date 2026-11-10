module
public import Guard.Extraction.Funs
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx ownership_nif ownership_nif.ownership_app
namespace Guard.Properties

theorem mutate (value accepted : Bool) :
    ownership_base.mutate_before_check value accepted = NativeM.ok
      ((if accepted then core.result.Result.Ok () else core.result.Result.Err ()), !value) := by
  cases accepted <;> simp [ownership_base.mutate_before_check, NativeM.ok]

theorem run_composes (guard : NativeGuard Bool) (accepted : Bool) :
    ownership_app.guard_panic guard accepted = (do
      let updated := { guard with value := !guard.value }
      if accepted then
        NativeGuard.release updated
        NativeM.ok (core.result.Result.Ok ())
      else
        NativeGuard.releasePanicking updated
        NativeM.ok (core.result.Result.Err ())) := by
  cases accepted <;>
    simp [ownership_app.guard_panic, mutate, NativeGuard.deref_mut, NativeM.lift, NativeM.ok,
      NativeDrop.drop, NativeUnwindDrop.drop]

theorem run_heap (guard : NativeGuard Bool) (accepted poisoned original : Bool)
    (env : Environment)
    (owner : guard.ownerContext = env.currentPid)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == guard.mutex.id) =
      [(guard.mutex.id, NativeMutex.typeName Bool,
        NativeMutex.lockedContents guard.ownerContext guard.token poisoned original)]) :
    ownership_app.guard_panic guard accepted env =
      (.ok (if accepted then core.result.Result.Ok () else core.result.Result.Err ()),
       { env with nativeHeap := env.nativeHeap.map fun cell =>
         if cell.1 == guard.mutex.id then
           (guard.mutex.id, NativeMutex.typeName Bool,
            .tuple #[.atom "unlocked",
              .atom (if poisoned || !accepted then "poisoned" else "unpoisoned"),
              NativeCodec.encode (!guard.value)])
         else cell }) := by
  rw [run_composes]
  cases accepted
  · simpa [NativeM.ok] using
      (NativeGuard.releasePanicking_owned_next {guard with value := !guard.value}
        original poisoned (NativeM.ok (.Err ()) : NativeM (core.result.Result Unit Unit))
        env owner stored)
  · simpa [NativeM.ok] using
      (NativeGuard.release_owned_next {guard with value := !guard.value}
        original poisoned (NativeM.ok (.Ok ()) : NativeM (core.result.Result Unit Unit))
        env owner stored)

@[expose] def initial : Environment := {}

theorem local_scope (value accepted : Bool) :
    ownership_app.local_guard_panic value accepted initial =
      (.ok (if accepted then core.result.Result.Ok true else core.result.Result.Err ()),
       { initial with nativeRefCounter := 2 }) := by
  let allocated : Environment := { initial with
    nativeRefCounter := 1
    nativeHeap := [(1, NativeMutex.typeName Bool,
      .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])] }
  have acquired := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex Bool) value false
    allocated (by simp [allocated]) (by simp [allocated])
  simp only [allocated, initial] at acquired
  cases accepted <;>
    simp [ownership_app.local_guard_panic, ownership_app.consume_guard_panic,
      run_composes, NativeMutex.new, NativeMutex.lock, NativeM.allocate,
      NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop, initial]
  all_goals rw [Result.wait_ready_run _ _ _ _ _ acquired]
  all_goals simp [NativeGuard.release, NativeGuard.releasePanicking, NativeM.ok]
  · rw [Result.wait_ready_run _ _ _ _ _
      (NativeGuard.pollReleasePanicking_owned
        (⟨⟨1⟩, 2, [], !value⟩ : NativeGuard Bool) value false
        { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool, NativeMutex.lockedContents [] 2 false value)] }
        rfl (by simp))]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      NativeCodec.roundtrip, initial]
  · have ready : NativeGuard.pollRelease
        (⟨⟨1⟩, 2, [], !value⟩ : NativeGuard Bool)
        { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool, NativeMutex.lockedContents [] 2 false value)] } =
        some (.ok (), { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool,
            .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (!value)])] }) := by
      simp [NativeGuard.pollRelease, NativeMutex.lockedContents, NativeCodec.roundtrip]
    rw [Result.wait_ready_run _ _ _ _ _ ready]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      NativeCodec.roundtrip, initial]

end Guard.Properties

namespace Guard.Properties
/-- The actual runtime adapter preserves cleanup before converting a Rust panic. -/
theorem adapter_continuation {β : Type} (value accepted : Bool) (next : Term → Result β) (schedule : List ScheduleChoice) :
    (do
      let encoded ← Rustler.executeNative
        (NativeM.resumeCaptured (__GUARDED__ value accepted)) Rustler.encodeBool
      next encoded).run initial schedule =
      if accepted then (next Term.true).run { initial with nativeRefCounter := 2 } schedule
      else (.error (.error (.atom "nif_panicked")), { initial with nativeRefCounter := 2 }) := by
  let allocated : Environment := { initial with
    nativeRefCounter := 1
    nativeHeap := [(1, NativeMutex.typeName Bool,
      .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])] }
  have acquired := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex Bool) value false
    allocated (by simp [allocated]) (by simp [allocated])
  simp only [allocated, initial] at acquired
  cases accepted <;>
    simp [__GUARDED__, Rustler.executeNative, NativeM.resumeCaptured, NativeM.fail, Result.handle,
      ownership_app.local_guard_panic, ownership_app.consume_guard_panic,
      run_composes, NativeMutex.new, NativeMutex.lock, NativeM.allocate,
      NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop, initial]
  all_goals rw [Result.wait_ready_run _ _ _ _ _ acquired schedule]
  all_goals simp [NativeGuard.release, NativeGuard.releasePanicking, NativeM.ok, Result.handle, Result.bind]
  · rw [Result.wait_ready_run _ _ _ _ _
      (NativeGuard.pollReleasePanicking_owned
        (⟨⟨1⟩, 2, [], !value⟩ : NativeGuard Bool) value false
        { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool, NativeMutex.lockedContents [] 2 false value)] }
        rfl (by simp)) schedule]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      NativeCodec.roundtrip, Result.handle, Rustler.encodeBool, initial]
  · have ready : NativeGuard.pollRelease
        (⟨⟨1⟩, 2, [], !value⟩ : NativeGuard Bool)
        { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool, NativeMutex.lockedContents [] 2 false value)] } =
        some (.ok (), { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool,
            .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (!value)])] }) := by
      simp [NativeGuard.pollRelease, NativeMutex.lockedContents, NativeCodec.roundtrip]
    rw [Result.wait_ready_run _ _ _ _ _ ready schedule]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      NativeCodec.roundtrip, Result.handle, Rustler.encodeBool, initial]

end Guard.Properties

namespace Guard.Properties
/-- A surrounding Elixir handler observes panic only after the actual cleanup. -/
theorem handler_prefix {β γ : Type} (value accepted : Bool)
    (tail : Term → Result β) (next : β → Result γ) (handler : Exception → Result γ) (schedule : List ScheduleChoice) :
    (Result.tryWith (do
      let encoded ← Rustler.executeNative
        (NativeM.resumeCaptured (__GUARDED__ value accepted)) Rustler.encodeBool
      tail encoded) next handler).run initial schedule =
      if accepted then (Result.tryWith (tail Term.true) next handler).run { initial with nativeRefCounter := 2 } schedule
      else (handler (.error (.atom "nif_panicked"))).run { initial with nativeRefCounter := 2 } schedule := by
  let allocated : Environment := { initial with
    nativeRefCounter := 1
    nativeHeap := [(1, NativeMutex.typeName Bool,
      .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode value])] }
  have acquired := NativeMutex.pollLock_unlocked (⟨1⟩ : NativeMutex Bool) value false
    allocated (by simp [allocated]) (by simp [allocated])
  simp only [allocated, initial] at acquired
  cases accepted <;>
    simp [__GUARDED__, Rustler.executeNative, NativeM.resumeCaptured, NativeM.fail, Result.tryWith, Result.handle, Result.bind,
      ownership_app.local_guard_panic, ownership_app.consume_guard_panic,
      run_composes, NativeMutex.new, NativeMutex.lock, NativeM.allocate,
      NativeM.ok, NativeDrop.drop, NativeUnwindDrop.drop, initial]
  all_goals rw [Result.wait_ready_run _ _ _ _ _ acquired schedule]
  all_goals simp [NativeGuard.release, NativeGuard.releasePanicking, NativeM.ok, Result.handle, Result.bind]
  · rw [Result.wait_ready_run _ _ _ _ _
      (NativeGuard.pollReleasePanicking_owned
        (⟨⟨1⟩, 2, [], !value⟩ : NativeGuard Bool) value false
        { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool, NativeMutex.lockedContents [] 2 false value)] }
        rfl (by simp)) schedule]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      NativeCodec.roundtrip, Result.tryWith, Result.handle, Result.bind, Rustler.encodeBool, initial]
  · have ready : NativeGuard.pollRelease
        (⟨⟨1⟩, 2, [], !value⟩ : NativeGuard Bool)
        { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool, NativeMutex.lockedContents [] 2 false value)] } =
        some (.ok (), { nativeRefCounter := 2, nativeHeap :=
          [(1, NativeMutex.typeName Bool,
            .tuple #[.atom "unlocked", .atom "unpoisoned", NativeCodec.encode (!value)])] }) := by
      simp [NativeGuard.pollRelease, NativeMutex.lockedContents, NativeCodec.roundtrip]
    rw [Result.wait_ready_run _ _ _ _ _ ready schedule]
    simp [NativeMutex.dispose, NativeM.readCell, NativeM.removeCell, NativeM.ok,
      NativeCodec.roundtrip, Result.tryWith, Result.handle, Result.bind, Rustler.encodeBool, initial]

end Guard.Properties
