module
public import Runtime.PayloadFacade.Funs
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Runtime.PayloadFacadeProperties

/-- The actual NIF's compiler cleanup runs before either continuation or handler. -/
theorem handler_spec {β : Type} (value : U64) (accepted : Bool)
    (next : Term → Result β) (handler : Exception → Result β)
    (env : Environment) (empty : env.nativeHeap = []) (schedule : List ScheduleChoice) :
    (Result.tryWith (Rustler.executeNative (__NIF__ value accepted) Rustler.encodeBool)
      next handler).run env schedule =
      if accepted then (next Term.true).run { env with nativeRefCounter := env.nativeRefCounter + 1 } schedule
      else (handler (.error (.atom "nif_panicked"))).run { env with nativeRefCounter := env.nativeRefCounter + 1 } schedule := by
  cases accepted <;>
    simp [__NIF__, mutex_assert, Rustler.executeNative, Result.tryWith, Result.handle,
      Result.bind, NativeMutex.new, NativeM.allocate, NativeDrop.drop, NativeMutex.dispose,
      NativeM.readCell, NativeM.removeCell, NativeCodec.roundtrip,
      NativeM.fail, NativeM.ok, empty, Rustler.encodeBool]

/-- Additional protected work runs only after successful native completion. -/
theorem handler_prefix_spec {β γ : Type} (value : U64) (accepted : Bool)
    (tail : Term → Result β) (next : β → Result γ) (handler : Exception → Result γ)
    (env : Environment) (empty : env.nativeHeap = []) (schedule : List ScheduleChoice) :
    (Result.tryWith (do
      let encoded ← Rustler.executeNative (__NIF__ value accepted) Rustler.encodeBool
      tail encoded) next handler).run env schedule =
      if accepted then (Result.tryWith (tail Term.true) next handler).run { env with nativeRefCounter := env.nativeRefCounter + 1 } schedule
      else (handler (.error (.atom "nif_panicked"))).run { env with nativeRefCounter := env.nativeRefCounter + 1 } schedule := by
  cases accepted <;>
    simp [__NIF__, mutex_assert, Rustler.executeNative, Result.tryWith, Result.handle,
      Result.bind, NativeMutex.new, NativeM.allocate, NativeDrop.drop, NativeMutex.dispose,
      NativeM.readCell, NativeM.removeCell, NativeCodec.roundtrip,
      NativeM.fail, NativeM.ok, empty, Rustler.encodeBool]


end Runtime.PayloadFacadeProperties
