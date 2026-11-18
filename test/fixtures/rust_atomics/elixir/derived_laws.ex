defmodule LynxDerivedNativeFixture.Laws do
  @compile :debug_info
  use Lynx.Laws

  law matched,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)
        returned = LynxDerivedNativeFixture.Native.atomic_tuple(resource, {7, 11}) == {true, 7}
        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 11
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode
        (.tuple #[.integer 7, .integer 11]) =
          Lynx.NativeM.ok (.Ok {expected := 7#u64, replacement := 11#u64}) := by
      exact Derived.Properties.decoder_success 7#u64 11#u64
    simp only [Lynx.apply, «matched:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law mismatch,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)
        returned = LynxDerivedNativeFixture.Native.atomic_tuple(resource, {8, 11}) == {false, 7}
        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode
        (.tuple #[.integer 8, .integer 11]) =
          Lynx.NativeM.ok (.Ok {expected := 8#u64, replacement := 11#u64}) := by
      exact Derived.Properties.decoder_success 8#u64 11#u64
    simp only [Lynx.apply, «mismatch:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law not_tuple,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDerivedNativeFixture.Native.atomic_tuple(resource, :invalid)
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.atom "invalid") = Lynx.NativeM.ok (.Err Lynx.Rustler.badArgOutcome) := by
      exact Derived.Properties.non_tuple _ (by intro fields; intro impossible; cases impossible)
    simp only [Lynx.apply, «not_tuple:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law short_tuple,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDerivedNativeFixture.Native.atomic_tuple(resource, {false})
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.tuple #[.atom "false"]) = Lynx.NativeM.ok (.Err Lynx.Rustler.badArgOutcome) := by
      apply Derived.Properties.arity_rejected
      · decide
      · constructor
        · scalar_tac
        · constructor <;> scalar_tac
    simp only [Lynx.apply, «short_tuple:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law long_tuple,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDerivedNativeFixture.Native.atomic_tuple(resource, {7, 11, 13})
            false
          catch
            :error, :badarg -> true
          end

        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.tuple #[.integer 7, .integer 11, .integer 13]) = Lynx.NativeM.ok (.Err Lynx.Rustler.badArgOutcome) := by
      apply Derived.Properties.arity_rejected
      · decide
      · constructor
        · scalar_tac
        · constructor <;> scalar_tac
    simp only [Lynx.apply, «long_tuple:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law expected_error,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDerivedNativeFixture.Native.atomic_tuple(resource, {false, 11})
            false
          catch
            :error, reason -> reason == "Could not decode field expected on Request"
          end

        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.tuple #[.atom "false", .integer 11]) =
        Lynx.NativeM.ok (.Err (.encoded true (fun _ =>
          Aeneas.Std.RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0))
          (Aeneas.Std.RustM.ok ()))) := by
      have size : "Could not decode field expected on Request".utf8ByteSize ≤ 4294967295 := by decide +kernel
      have encoded (env : Lynx.Rustler.Env) :
          Lynx.Rustler.Encoding.string "Could not decode field expected on Request" env =
            Aeneas.Std.RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0) := by
        simp [Lynx.Rustler.Encoding.string, size]
        decide +kernel
      simpa only [Lynx.Rustler.raiseTermErrorOutcome,
        atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
        encoded] using
        Derived.Properties.decoder_expected_error (.atom "false") (.integer 11) (by rfl)
    simp only [Lynx.apply, «expected_error:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law replacement_error,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDerivedNativeFixture.Native.atomic_tuple(resource, {7, -1})
            false
          catch
            :error, reason -> reason == "Could not decode field replacement on Request"
          end

        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.tuple #[.integer 7, .integer (-1)]) =
        Lynx.NativeM.ok (.Err (.encoded true (fun _ =>
          Aeneas.Std.RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0))
          (Aeneas.Std.RustM.ok ()))) := by
      have size : "Could not decode field replacement on Request".utf8ByteSize ≤ 4294967295 := by decide +kernel
      have encoded (env : Lynx.Rustler.Env) :
          Lynx.Rustler.Encoding.string "Could not decode field replacement on Request" env =
            Aeneas.Std.RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 114, 101, 112, 108, 97, 99, 101, 109, 101, 110, 116, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0) := by
        simp [Lynx.Rustler.Encoding.string, size]
        decide +kernel
      have input : Lynx.Rustler.encodeUnsigned 7#u64 = .integer 7 := by
        simp [Lynx.Rustler.encodeUnsigned]
      simpa only [Lynx.Rustler.raiseTermErrorOutcome,
        atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
        input, encoded] using
        Derived.Properties.decoder_replacement_error 7#u64 (.integer (-1)) (by rfl)
    simp only [Lynx.apply, «replacement_error:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law first_error_wins,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(7)

        returned =
          try do
            LynxDerivedNativeFixture.Native.atomic_tuple(resource, {false, :invalid})
            false
          catch
            :error, reason -> reason == "Could not decode field expected on Request"
          end

        returned and LynxDerivedNativeFixture.Native.atomic_read(resource) == 7
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode (.tuple #[.atom "false", .atom "invalid"]) =
        Lynx.NativeM.ok (.Err (.encoded true (fun _ =>
          Aeneas.Std.RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0))
          (Aeneas.Std.RustM.ok ()))) := by
      have size : "Could not decode field expected on Request".utf8ByteSize ≤ 4294967295 := by decide +kernel
      have encoded (env : Lynx.Rustler.Env) :
          Lynx.Rustler.Encoding.string "Could not decode field expected on Request" env =
            Aeneas.Std.RustM.ok (.bitstring ⟨#[67, 111, 117, 108, 100, 32, 110, 111, 116, 32, 100, 101, 99, 111, 100, 101, 32, 102, 105, 101, 108, 100, 32, 101, 120, 112, 101, 99, 116, 101, 100, 32, 111, 110, 32, 82, 101, 113, 117, 101, 115, 116]⟩ 0) := by
        simp [Lynx.Rustler.Encoding.string, size]
        decide +kernel
      simpa only [Lynx.Rustler.raiseTermErrorOutcome,
        atomic_nif.alloc.string.String.Insts.RustlerTypesEncoder,
        encoded] using
        Derived.Properties.decoder_expected_error (.atom "false") (.atom "invalid") (by rfl)
    simp only [Lynx.apply, «first_error_wins:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """

  law maximum,
    expects:
      (
        resource = LynxDerivedNativeFixture.Native.atomic_new(18_446_744_073_709_551_615)

        LynxDerivedNativeFixture.Native.atomic_tuple(resource, {18_446_744_073_709_551_615, 0}) ==
          {true, 18_446_744_073_709_551_615} and
          LynxDerivedNativeFixture.Native.atomic_read(resource) == 0
      ),
    proof: ~LEAN"""
    set_option maxHeartbeats 16000000 in
    set_option maxRecDepth 8192 in
    have decoded : atomic_nif.derived.Request.Insts.RustlerTypesDecoder.decode
        (.tuple #[.integer 18446744073709551615, .integer 0]) =
          Lynx.NativeM.ok (.Ok {expected := 18446744073709551615#u64, replacement := 0#u64}) := by
      exact Derived.Properties.decoder_success 18446744073709551615#u64 0#u64
    simp only [Lynx.apply, «maximum:ensures/0»,
      Elixir.LynxDerivedNativeFixture.Native.«atomic_tuple/2», decoded]
    refine ⟨0, ?_⟩
    intro depth enough elapsed events last outcome run terminal
    apply terminal.outcome_eq.symm.trans
    apply Lynx.Outcome.eq_of_isTrue
    apply Lynx.Concurrent.checkPost_sound (depth := 384)
      (accept := fun config => config.outcome.isTrue) ?_ run terminal
    clear enough events last outcome run terminal
    lynx_check_post
    """
end
