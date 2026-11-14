module
public import Shared.FramedTermAdapter
public import Shared.Future
public section
open Aeneas Aeneas.Std Lynx effects_native
open Shared.FramedTermAdapter
namespace Shared.FramedFutureAdapter
set_option maxRecDepth 8192

/-- The actual twice-polled driver has the proven immediate driver's effect. -/
@[simp] theorem resume_adapter_equal (dispatcher : Dispatcher) (term amount : Term) :
    Elixir.LynxEffectsFixture.Native.«counter_poll_resume/2» dispatcher term amount =
      Elixir.LynxEffectsFixture.Native.«counter_poll_add/2» dispatcher term amount := by
  rw [Elixir.LynxEffectsFixture.Native.«counter_poll_resume:adapter/2»,
    Elixir.LynxEffectsFixture.Native.«counter_poll_add:adapter/2»]
  simp only [Shared.Future.resume_contract]

private theorem adapter_cancel_valid (dispatcher : Dispatcher) (term : Nat) (amount : U64) : Elixir.LynxEffectsFixture.Native.«counter_poll_cancel/2» dispatcher (.nativeReference term)
      (Rustler.encodeUnsigned amount) = Rustler.withResourceTypes [NativeResourceArc.typeName CounterResource] (do
        let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
        Rustler.executeNative (__CANCEL__ owner amount) Rustler.encodeBool) := by
  have decoded : Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned amount) = .ok amount :=
    Rustler.decodeUnsigned_encodeUnsigned amount
  rw [Elixir.LynxEffectsFixture.Native.«counter_poll_cancel:adapter/2»]
  conv_rhs =>
    arg 1
    simp only [NativeResourceArc.typeName,
      Shared.Extraction.NativeCodecs.«typeName::effects_native::CounterResource»]
    cbv
  apply congrArg (Rustler.withResourceTypes _)
  apply congrArg (fun continuation =>
    NativeResourceArc.decode (α := CounterResource) (.nativeReference term) >>= continuation)
  funext owner
  rw [decoded]
  simp only [Result.ofExcept,Result.handle,Result.ok_bind]

private theorem registration_prefix {α : Type} (body : Result α) (env : Environment) :
    Result.ReadyPrefix (Rustler.withResourceTypes [NativeResourceArc.typeName CounterResource] body)
      env body (registeredEnv env) := by
  unfold Rustler.withResourceTypes
  exact .nativeModify _ _ () _ _ _ _ rfl (.refl _ _)

/-- Cancelling the actual Pending future consumes the temporary captured owner.
Other owners and the shared value remain available to the next native call. -/
theorem owned_cancel_prefix (dispatcher : Dispatcher) (value amount : U64) (counter : Nat)
    (counterBound : 44 ≤ counter) :
    Result.ReadyPrefix (Elixir.LynxEffectsFixture.Native.«counter_poll_cancel/2» dispatcher
      (.nativeReference 5) (Rustler.encodeUnsigned amount))
      (owned value counter) (.ok Term.true) (owned value (counter + 1)) := by
  have trace := Shared.FramedCalls.release_call_prefix
    (⟨2,4⟩ : NativeResourceArc CounterResource) 5 ({state := ⟨1⟩} : CounterResource) 3
    (registeredEnv (owned value counter)) (fun owner => __CANCEL__ owner amount) true Rustler.encodeBool
    (fun owner => Shared.Future.cancel_contract owner amount)
    (by simp [registeredEnv]) (by decide) (by decide)
    (by simp [registeredEnv,owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells]; omega)
    (by simp [registeredEnv,owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [registeredEnv,owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [registeredEnv,owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [registeredEnv,owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeMutex.typeName])
  rw [adapter_cancel_valid dispatcher 5 amount]
  have combined := (registration_prefix _ (owned value counter)).trans trace
  have dedup : [NativeResourceArc.typeName CounterResource,NativeResourceArc.typeName CounterResource].eraseDups =
      [NativeResourceArc.typeName CounterResource] := by cbv
  simpa [owned,registeredEnv,dedup,Shared.Properties.Framed.initialFor,Rustler.encodeBool] using combined

end Shared.FramedFutureAdapter
