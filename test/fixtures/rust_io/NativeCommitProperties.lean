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

end Publish.Native
