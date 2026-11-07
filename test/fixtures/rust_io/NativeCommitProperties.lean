module
public import Publish.Framed
public import Publish.RustlerBridge
public section
open Aeneas Aeneas.Std Lynx io_native
namespace Publish.Native

/-- The compiled Rustler entry calls the extracted first-party protocol. -/
theorem facade_prefix (value : U16) (env : Environment)
    (counter : env.refCounter = Publish.Commit.initial.refCounter)
    (heap : env.nativeHeap = Publish.Commit.initial.nativeHeap) :
    Result.ReadyPrefix (__COMMIT__ value) env (.ok true)
      {env with refCounter := (Publish.Commit.done value).refCounter, nativeHeap := (Publish.Commit.done value).nativeHeap} := by
  simpa [__COMMIT__,monadLift_self] using
    Publish.Commit.Framed.acknowledged_prefix value env counter heap

/-- Encoding and native exception conversion preserve the actual publication prefix. -/
theorem adapter_continuation {β : Type} (value : U16) (next : Term → Result β)
    (env : Environment)
    (counter : env.refCounter = Publish.Commit.initial.refCounter)
    (heap : env.nativeHeap = Publish.Commit.initial.nativeHeap) :
    (Rustler.executeNative (__COMMIT__ value)
      Rustler.encodeBool >>= next) env =
    next Term.true {env with refCounter := (Publish.Commit.done value).refCounter, nativeHeap := (Publish.Commit.done value).nativeHeap} := by
  have trace := Rustler.executeNative_readyPrefix (facade_prefix value env counter heap) Rustler.encodeBool
  simpa [Rustler.encodeBool] using (trace.bind next).apply



/-- Failure consumes the admitted error before returning through the compiled facade. -/
theorem rejected_facade_prefix (value : U16) (env : Environment)
    (counter : env.refCounter = Publish.IoErrors.rejected.refCounter)
    (heap : env.nativeHeap = Publish.IoErrors.rejected.nativeHeap) :
    Result.ReadyPrefix (__COMMIT__ value) env (.ok false)
      {env with nativeHeap := Publish.IoErrors.disposed.nativeHeap} := by
  simpa [__COMMIT__,monadLift_self] using
    Publish.Commit.Framed.rejected_prefix value env counter heap

/-- The Elixir continuation receives false after actual native error destruction. -/
theorem rejected_adapter_continuation {β : Type} (value : U16) (next : Term → Result β)
    (env : Environment)
    (counter : env.refCounter = Publish.IoErrors.rejected.refCounter)
    (heap : env.nativeHeap = Publish.IoErrors.rejected.nativeHeap) :
    (Rustler.executeNative (__COMMIT__ value) Rustler.encodeBool >>= next) env =
    next Term.false {env with nativeHeap := Publish.IoErrors.disposed.nativeHeap} := by
  have trace := Rustler.executeNative_readyPrefix (rejected_facade_prefix value env counter heap) Rustler.encodeBool
  simpa [Rustler.encodeBool] using (trace.bind next).apply

/-- The error cleanup also composes through a real protected Elixir computation. -/
theorem rejected_handler_prefix {β γ : Type} (value : U16)
    (tail : Term → Result β) (next : β → Result γ) (handler : Exception → Result γ)
    (env : Environment)
    (counter : env.refCounter = Publish.IoErrors.rejected.refCounter)
    (heap : env.nativeHeap = Publish.IoErrors.rejected.nativeHeap) :
    Result.tryWith (Rustler.executeNative (__COMMIT__ value) Rustler.encodeBool >>= tail)
      next handler env =
    Result.tryWith (tail Term.false) next handler
      {env with nativeHeap := Publish.IoErrors.disposed.nativeHeap} := by
  have trace := Rustler.executeNative_readyPrefix (rejected_facade_prefix value env counter heap) Rustler.encodeBool
  simpa [Rustler.encodeBool] using ((trace.bind tail).tryWith next handler).apply

/-- A custom error payload does not satisfy the callback-free OS-error admission. -/
@[expose] def customRejected : Environment :=
  {Publish.IoErrors.rejected with nativeHeap := Publish.IoErrors.rejected.nativeHeap.map fun cell =>
    if cell.1 == 1 then (cell.1,cell.2.1,.atom "custom") else cell}

end Publish.Native
