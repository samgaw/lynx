module
public import Encoded.Extraction.Funs
public import Encoded.RustlerBridge
public meta import LynxTest.ProofAudit
public section
open Aeneas Aeneas.Std Lynx atomic_nif
namespace Encoded.Properties
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem encoder_spec (value : encoding.Reply) (env : Rustler.Env) :
    encoding.Reply.Insts.RustlerTypesEncoder.encode value env =
      NativeM.ok (.tuple #[Rustler.encodeUnsigned value.previous, Rustler.encodeUnsigned value.current]) := by
  simp [encoding.Reply.Insts.RustlerTypesEncoder.encode,
    Rustler.Encoding.u64, Rustler.Encoding.makeTuple, Rustler.encodeUnsigned,
    Array.to_slice, Array.make, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem checked_encoder (value : U64) (nonzero : value ≠ 0#u64) (env : Rustler.Env) :
    encoding.CheckedReply.Insts.RustlerTypesEncoder.encode {value} env =
      NativeM.ok (Rustler.encodeUnsigned value) := by
  simp [encoding.CheckedReply.Insts.RustlerTypesEncoder.encode,
    nonzero, Rustler.Encoding.u64, Rustler.encodeUnsigned, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem checked_panics (env : Rustler.Env) :
    encoding.CheckedReply.Insts.RustlerTypesEncoder.encode {value := 0#u64} env =
      NativeM.fail .panic := by
  simp [encoding.CheckedReply.Insts.RustlerTypesEncoder.encode,
    RustFormatting.core.fmt.Arguments.from_str, NativeM.lift, NativeM.fromRust, NativeM.ok]

theorem checked_spec (value : encoding.CheckedReply) (env : Rustler.Env) :
    encoding.CheckedReply.Insts.RustlerTypesEncoder.encode value env =
      if value.value = 0#u64 then NativeM.fail .panic
      else NativeM.ok (Rustler.encodeUnsigned value.value) := by
  rcases value with ⟨value⟩
  by_cases zero : value = 0#u64
  · subst value
    simpa using checked_panics env
  · simp [zero, checked_encoder value zero env]

/-- An absent optional result does not run even a panicking Encoder. -/
theorem absent_encoder {α : Type} (encode : α → Result Term) :
    Rustler.encodeNativeOptionM encode none = .ok (.atom "nil") := by rfl

/-- The unselected result Encoder contributes no effects. -/
theorem error_encoder {α β : Type} (encodeOk : α → Result Term) (encodeErr : β → Result Term) (value : β) :
    Rustler.encodeNativeResultM encodeOk encodeErr (.Err value) = (do
      let encoded ← encodeErr value
      .ok (.tuple #[.atom "error", encoded])) := by rfl

theorem contract (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_core.replace counter expected replacement =
      NativeAtomic.compareExchange counter expected replacement .SeqCst .SeqCst := by rfl

theorem composed (counter : NativeAtomic U64 (NativeAtomicStorage U64)) (expected replacement : U64) :
    atomic_analysis.try_set counter expected replacement = (do
      let result ← atomic_core.replace counter expected replacement
      match result with
      | .Ok previous => NativeM.ok (true, previous)
      | .Err observed => NativeM.ok (false, observed)) := by rfl

theorem reference_eq (left right : Nat) :
    (Term.nativeReference left == Term.nativeReference right) = (left == right) := by
  apply Bool.eq_iff_iff.mpr
  rw [Term.beq_iff_compare_eq, Term.compare_eq_reference]
  simp

@[expose] def retained (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := [
      (4,NativeResourceArc.handleType Counter,.nativeReference 2),
      (3,NativeResourceArc.handleType Counter,.nativeReference 2),
      (2,NativeResourceArc.typeName Counter,
        .tuple #[.integer 2,NativeCodec.encode ({state := ⟨1⟩} : Counter)]),
      (1,NativeAtomic.typeName,NativeCodec.encode value)] }

@[expose] def afterCall (value : U64) : Environment :=
  { nativeRefCounter := 4
    nativeResourceTypes := [NativeResourceArc.typeName Counter]
    nativeHeap := [
      (4,NativeResourceArc.handleType Counter,.nativeReference 2),
      (2,NativeResourceArc.typeName Counter,
        .tuple #[.integer 1,NativeCodec.encode ({state := ⟨1⟩} : Counter)]),
      (1,NativeAtomic.typeName,NativeCodec.encode value)] }

theorem matched (previous replacement : U64) (schedule : List ScheduleChoice) :
    (encoding.counter_reply ⟨2,3⟩ previous replacement).run (retained previous) schedule =
      (.ok {previous, current := replacement}, afterCall replacement) := by
  simp [encoding.counter_reply, composed, contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

theorem mismatch (previous expected replacement : U64) (different : previous ≠ expected)
    (schedule : List ScheduleChoice) :
    (encoding.counter_reply ⟨2,3⟩ expected replacement).run (retained previous) schedule =
      (.ok {previous, current := previous}, afterCall previous) := by
  simp [encoding.counter_reply, composed, contract, retained, afterCall,
    NativeResourceArc.deref, NativeResourceArc.releaseOwned,
    NativeResourceArc.ownedState, NativeResourceArc.ownerState, NativeResourceArc.ownership,
    NativeResourceArc.retiredState, NativeResourceArc.typeName, NativeResourceArc.handleType,
    NativeResourceArc.referenceLimit, NativeResourceCleanup.cleanup, NativeResourceCleanup.observable,
    NativeAtomic.lookup, NativeAtomic.update, NativeAtomic.compareExchange, NativeAtomic.dispose,
    NativeAtomic.typeName, NativeOwnedDrop.drop, NativeM.ok, NativeM.fail, NativeM.lift,
    NativeCodec.roundtrip, reference_eq, different, Result.handle, Result.bind, Result.ofExcept,
    List.filter_cons, List.filter_nil]
  all_goals first | rfl | decide

end Encoded.Properties
