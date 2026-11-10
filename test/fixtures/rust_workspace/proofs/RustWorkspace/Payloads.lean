module
public import Payloads.Extraction.Funs
public import Payloads.RustlerBridge
public section
open Aeneas Aeneas.Std experiment_nif
namespace Payloads.Properties

theorem invert_spec (value : Bool) : experiment_core.invert value = RustM.ok (!value) := by
  cases value <;> rfl

theorem restore_spec (value : Bool) : experiment_analysis.restore value = RustM.ok value := by
  cases value <;> simp [experiment_analysis.restore, invert_spec]

theorem encoder_spec (input : BoxedErrorPayload) (env : Lynx.Rustler.Env) :
    __ENCODER__ input env =
      if input.should_panic then RustM.fail .panic else RustM.ok (.integer input.value.val) := by
  cases h : input.should_panic <;>
    simp [__ENCODER__, restore_spec, h, Lynx.Rustler.Encoding.u64]

theorem raised_constructed (value : U64) (shouldPanic : Bool) :
    ∃ error, __RAISED__ value shouldPanic = RustM.ok (.Err error) := by
  exact ⟨_, rfl⟩

theorem returned_constructed (value : U64) (shouldPanic : Bool) :
    ∃ error, __RETURNED__ value shouldPanic = RustM.ok (.Err error) := by
  exact ⟨_, rfl⟩

theorem raised_spec (value : U64) (continuation : Bool → Except Lynx.Exception Lynx.Term) :
    Lynx.Rustler.Decoding.withDecoded (__RAISED__ value false) continuation =
      .error (.error (.integer value.val)) := by
  simp [__RAISED__, Lynx.Rustler.Decoding.withDecoded_error,
    Lynx.Rustler.raiseTermErrorOutcome, Lynx.Rustler.DecoderError.convert, encoder_spec]

theorem returned_spec (value : U64) (continuation : Bool → Except Lynx.Exception Lynx.Term) :
    Lynx.Rustler.Decoding.withDecoded (__RETURNED__ value false) continuation =
      .ok (.tuple #[.atom "error", .integer value.val]) := by
  simp [__RETURNED__, Lynx.Rustler.Decoding.withDecoded_error,
    Lynx.Rustler.termErrorOutcome, Lynx.Rustler.DecoderError.convert, encoder_spec]

theorem raised_panic (value : U64) (continuation : Bool → Except Lynx.Exception Lynx.Term) :
    Lynx.Rustler.Decoding.withDecoded (__RAISED__ value true) continuation = .error .exhausted := by
  simp [__RAISED__, Lynx.Rustler.Decoding.withDecoded_error,
    Lynx.Rustler.raiseTermErrorOutcome, Lynx.Rustler.DecoderError.convert, encoder_spec]

theorem returned_panic (value : U64) (continuation : Bool → Except Lynx.Exception Lynx.Term) :
    Lynx.Rustler.Decoding.withDecoded (__RETURNED__ value true) continuation = .error .exhausted := by
  simp [__RETURNED__, Lynx.Rustler.Decoding.withDecoded_error,
    Lynx.Rustler.termErrorOutcome, Lynx.Rustler.DecoderError.convert, encoder_spec]

end Payloads.Properties
