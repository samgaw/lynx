import LynxTest.ProofAudit
import Lynx.Rustler

namespace LynxTest.Rustler

theorem boolRoundtrip (value : Bool) :
    Lynx.Rustler.decodeBool (Lynx.Rustler.encodeBool value) = .ok value :=
  Lynx.Rustler.decodeBool_encodeBool value

theorem integerIsNotBool (value : Int) :
    Lynx.Rustler.decodeBool (.integer value) = .error (.error (.atom "badarg")) := rfl

theorem otherAtomIsNotBool (name : String) (ht : name ≠ "true") (hf : name ≠ "false") :
    Lynx.Rustler.decodeBool (.atom name) = .error (.error (.atom "badarg")) := by
  simp [Lynx.Rustler.decodeBool, ht, hf]

/-- Loader capabilities do not allocate or modify resource cells. -/
theorem registrationKeepsHeap (names : List String) (env : Lynx.Environment) :
    Lynx.Rustler.withResourceTypes names
      (.nativeGet fun loaded => Lynx.Result.ok loaded.nativeHeap) env =
      (.ok env.nativeHeap,
        { env with nativeResourceTypes := (env.nativeResourceTypes ++ names).eraseDups }) := by
  simp

theorem registrationPreservesExhaustion (names : List String) (env : Lynx.Environment) :
    Lynx.Rustler.withResourceTypes names (Lynx.Result.error .exhausted : Lynx.Result Unit) env =
      (.error .exhausted,
        { env with nativeResourceTypes := (env.nativeResourceTypes ++ names).eraseDups }) := by
  simp

private def registrationWork (name : String) : Lynx.Result Unit :=
  Lynx.Rustler.withResourceTypes [name] <|
    .nativeModify (fun env => ((), {env with
      nativeRefCounter := env.nativeRefCounter + 1,
      nativeHeap := env.nativeHeap.map fun cell => match cell with
        | (1, "counter", .integer value) => (1, "counter", .integer (value + 1))
        | other => other})) (fun _ => .ok ())

private def registrationRace (left right : String) : Lynx.Result Lynx.Term :=
  Lynx.Result.schedule {} (do
    registrationWork left
    Lynx.Result.send [] Lynx.Term.true (.ok .nil)) fun _ => do
      registrationWork right
      Lynx.Result.receive .infinity (fun _ message => some message) fun message =>
        .nativeGet fun env => .ok (
          if message == some Lynx.Term.true && env.nativeRefCounter == 4 &&
              env.nativeHeap == [(1, "counter", .integer 2), (2, "unrelated", .integer 17)] &&
              env.nativeResourceTypes.length == (["base", left, right].eraseDups).length &&
              env.nativeResourceTypes.contains "base" && env.nativeResourceTypes.contains left &&
              env.nativeResourceTypes.contains right &&
              (match env.nativeFinalizerMode with | .deferred => true | _ => false) then
            Lynx.Term.true else Lynx.Term.false)

/-- Registration must preserve peer effects and merge capabilities under every
transition order, not only when its read and write run consecutively. -/
theorem concurrentRegistrationKeepsPeerState :
    Lynx.Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 48
      (.start
        {nativeRefCounter := 2, nativeResourceTypes := ["base"], nativeFinalizerMode := .deferred,
          nativeHeap := [(1, "counter", .integer 0), (2, "unrelated", .integer 17)]}
        (registrationRace "left" "right")) = true := by cbv

/-- Reinstalling the same loaded type cannot roll back another call's heap or
identity updates, even though the registry's set of names is unchanged. -/
theorem repeatedRegistrationKeepsPeerState :
    Lynx.Concurrent.check (fun | .ok (.atom "true") => true | _ => false) 48
      (.start
        {nativeRefCounter := 2, nativeResourceTypes := ["base"], nativeFinalizerMode := .deferred,
          nativeHeap := [(1, "counter", .integer 0), (2, "unrelated", .integer 17)]}
        (registrationRace "resource" "resource")) = true := by cbv

theorem registeredCapability (names : List String) (env : Lynx.Environment)
    (name : String) (member : name ∈ names) :
    name ∈ (env.nativeResourceTypes ++ names).eraseDups :=
  Lynx.Rustler.registered_resource_type names env name member

/-- A native panic does not undo effects performed before the failure. -/
theorem nativePanicPreservesState (env updated : Lynx.Environment) :
    Lynx.Rustler.executeNative
      (Lynx.Result.nativeSet updated (.error (.error (.atom "rust_panicked"))) : Lynx.Result Lynx.Term)
      id env = (.error (.error (.atom "nif_panicked")), updated) := by
  simp [Lynx.Rustler.executeNative, Lynx.Result.handle]

/-- Unsupported native exceptions cannot become successful or catchable results. -/
theorem unsupportedNativeException :
    Lynx.Rustler.executeNative (.error (.throw .nil) : Lynx.Result Lynx.Term) id =
      .error .exhausted := rfl

/-- Blocking polls and their updates remain in the caller's runtime. -/
theorem nativeWaitPanic (poll : Lynx.Environment → Option (Unit × Lynx.Environment))
    (env updated : Lynx.Environment) (ready : poll env = some ((), updated)) :
    Lynx.Rustler.executeNative
      (.wait poll (fun _ => .error (.error (.atom "rust_panicked"))) : Lynx.Result Lynx.Term)
      id env = (.error (.error (.atom "nif_panicked")), updated) := by
  rw [Lynx.Rustler.executeNative_wait]
  rw [Lynx.Result.wait_ready_apply _ _ _ _ _ ready]
  rfl

run_cmd do
  LynxTest.ProofAudit.checkModule `Lynx.Rustler
  LynxTest.ProofAudit.checkModule `LynxTest.Rustler

end LynxTest.Rustler
