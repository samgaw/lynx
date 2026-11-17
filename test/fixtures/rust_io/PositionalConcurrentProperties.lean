module
public import Positional.Opened
import Lynx.Runner.CheckPost
public section
open Aeneas Aeneas.Std Lynx NativeFile
open Positional.Nif (Payload original zeros)
open Positional.Opened (inodeCell namespaceCell names)
open Positional.Properties (outcome)
namespace Positional.Concurrent

abbrev Patch := NativeResourceArc Payload → U64 → U8 → NativeM Bool
abbrev Observe := NativeResourceArc Payload → U64 → NativeM (Option U8)

@[expose] def writer : Term := .nativeReference 6
@[expose] def peer : Term := .nativeReference 11

@[expose] def pins : List (Nat × String × Term) :=
  NativeResourceArc.vmCells (⟨⟨2⟩⟩ : Payload) 3 5 6 ++
    NativeResourceArc.vmCells (⟨⟨7⟩⟩ : Payload) 8 10 11

@[expose] def descriptors (first second : Term) : List (Nat × String × Term) :=
  [(2, writableHandleTypeName, encodeHandle ⟨1, 1, first⟩),
   (7, writableHandleTypeName, encodeHandle ⟨1, 2, second⟩)]

@[expose] def frame (contents : ByteArray) (first second : Term) : List (Nat × String × Term) :=
  pins ++ descriptors first second ++ [namespaceCell names .nil, inodeCell contents]

@[expose] def ready : Environment :=
  let write := outcome "write_at" true 1 (zeros original)
  let sync := outcome "sync_data" true 0 ByteArray.empty
  let read := outcome "read_at" true 1 (zeros original) .nil
  { ({} : Environment).setPdict [(.atom "writer", writer), (.atom "peer", peer)] with
    nativeRefCounter := 11
    nativeResourceTypes := [NativeResourceArc.typeName Payload]
    nativeHeap := frame original (write (sync read)) (write (sync .nil)) }

/-- The abstract serial image for two acknowledged writes to byte zero.
The last writer supplies byte zero. Byte one is unaffected by both writes. -/
@[expose] def serialImage (last : UInt8) : ByteArray := ⟨#[last, 2]⟩

@[expose] def serialState (last : UInt8) (config : Lynx.Concurrent.Config Term) : Bool :=
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  let heap := frame (serialImage last) .nil .nil
  env.nativeRefCounter == 14 && env.nativeHeap.length == heap.length &&
    heap.all fun (expectedId, tag, value) =>
      env.nativeHeap.any fun (actualId, actualTag, actual) =>
        actualId == expectedId && actualTag == tag &&
          Term.compareExact (Term.fuel actual value) actual value == .eq

@[expose] def accepted (config : Lynx.Concurrent.Config Term) : Bool :=
  config.outcome.isTrue && (serialState 9 config || serialState 7 config)

@[expose] def acceptedObservation (config : Lynx.Concurrent.Config Term) : Bool :=
  match config.outcome with
  | .ok (.integer 9) => serialState 9 config
  | .ok (.integer 7) => serialState 7 config
  | _ => false

theorem accepted_outcome {config : Lynx.Concurrent.Config Term} (checked : accepted config = true) :
    config.outcome = .ok Term.true := by
  apply Outcome.eq_of_isTrue
  simp only [accepted, Bool.and_eq_true] at checked
  exact checked.1

@[expose] def patchCall (patch : Patch) (file : Term) (byte : U8) : Result Term := do
  let owner ← NativeResourceArc.decode file
  Rustler.executeNative (patch owner 0#u64 byte) Rustler.encodeBool

@[expose] def observeCall (observe : Observe) : Result Term := do
  let owner ← NativeResourceArc.decode writer
  Rustler.executeNative (observe owner 0#u64) (Rustler.encodeOption Rustler.encodeUnsigned)

@[expose] def program (patch : Patch) (observe : Observe) : Result Term := do
  let _ ← Result.schedule {} (do
    let reply ← patchCall patch peer 7#u8
    Result.send [] (.tuple #[.atom "patched", reply]) (.ok Term.true)) .ok
  let wrote ← patchCall patch writer 9#u8
  let peerReply ← Result.receive .infinity (fun _ term => match term with
    | .tuple fields => if fields[0]? == some (.atom "patched") then fields[1]? else none
    | _ => none) (fun reply => .ok (reply.getD Term.false))
  let read ← observeCall observe
  Result.ok (if wrote == Term.true && peerReply == Term.true then read else Term.false)

set_option maxHeartbeats 64000000 in
set_option maxRecDepth 8192 in
theorem patches_agree_with_serial_image (elapsed : PID → Nat → Nat)
    (events : List Lynx.Concurrent.Event)
    (last : Lynx.Concurrent.Config Term) (outcome : Outcome Term)
    (run : Lynx.Concurrent.Run (.start ready (program __PATCH__ __OBSERVE__) elapsed) events last)
    (terminal : Lynx.Concurrent.Terminal last outcome) :
    acceptedObservation last = true := by
  apply Lynx.Concurrent.checkPost_sound (depth := 256) ?_ run terminal
  clear events last outcome run terminal
  lynx_check_post

open Lynx.Concurrent (Config Event Run Step Terminal)

private def ordered (lastFirst : Bool) (config : Config Term) : List (Event × Config Term) :=
  if lastFirst then config.successors.reverse else config.successors

private def follow (lastFirst : Bool) : Nat → Config Term → Option (List Event × Config Term)
  | 0, _ => none
  | fuel + 1, config =>
      match ordered lastFirst config with
      | [] => some ([], config)
      | (event, next) :: _ => do
          let (events, final) ← follow lastFirst fuel next
          some (event :: events, final)

private theorem follow_sound {lastFirst : Bool} {fuel : Nat} {first last : Config Term}
    {events : List Event} (found : follow lastFirst fuel first = some (events, last)) :
    Run first events last ∧ last.successors = [] := by
  induction fuel generalizing first last events with
  | zero => simp [follow] at found
  | succ fuel ih =>
    cases order : ordered lastFirst first with
    | nil =>
      simp [follow, order] at found
      obtain ⟨rfl, rfl⟩ := found
      exact ⟨.refl, by cases lastFirst <;> simpa [ordered] using order⟩
    | cons head tail =>
      obtain ⟨event, next⟩ := head
      cases result : follow lastFirst fuel next with
      | none => simp [follow, order, result] at found
      | some resumed =>
        obtain ⟨rest, final⟩ := resumed
        simp [follow, order, result] at found
        obtain ⟨rfl, rfl⟩ := found
        obtain ⟨run, done⟩ := ih result
        have member : (event, next) ∈ ordered lastFirst first := by
          rw [order]
          exact List.mem_cons_self
        have nextStep : Step first event next := by
          cases lastFirst <;> simpa [Step, ordered] using member
        exact ⟨.step nextStep run, done⟩

private def returns (expected : Int) (config : Config Term) : Bool :=
  match config.outcome with
  | .ok (.integer actual) => actual == expected
  | _ => false

private theorem returns_eq {expected : Int} {config : Config Term}
    (matched : returns expected config = true) : config.outcome = .ok (.integer expected) := by
  unfold returns at matched
  split at matched
  next actual outcome =>
    rw [beq_iff_eq] at matched
    simp [outcome, matched]
  next => simp at matched

private theorem terminal_witness {first : Config Term} {expected : Int} {lastFirst : Bool}
    (checked : (follow lastFirst 64 first).any (fun (_, last) => returns expected last) = true) :
    ∃ events last, Run first events last ∧ Terminal last (.ok (.integer expected)) := by
  cases found : follow lastFirst 64 first with
  | none => simp [found] at checked
  | some terminal =>
    obtain ⟨events, last⟩ := terminal
    have ⟨run, stopped⟩ := follow_sound found
    have outcome : last.outcome = .ok (.integer expected) :=
      returns_eq (by simpa [found] using checked)
    exact ⟨events, last, run, outcome ▸ Terminal.stuck stopped⟩


set_option maxHeartbeats 4000000 in
/-- A concrete sequence of model steps reaches the peer's serial image. -/
theorem peer_byte_reachable (elapsed : PID → Nat → Nat) :
    ∃ events last, Run (.start ready (program
        __PATCH__
        __OBSERVE__) elapsed)
      events last ∧ Terminal last (.ok (.integer 7)) ∧ serialState 7 last = true := by
  obtain ⟨events, last, run, done⟩ := terminal_witness (lastFirst := false)
    (expected := 7) (first := .start ready (program
      __PATCH__
      __OBSERVE__) elapsed) (by cbv)
  have correct := patches_agree_with_serial_image elapsed events last _ run done
  exact ⟨events, last, run, done, by simpa only [acceptedObservation, done.outcome_eq] using correct⟩

set_option maxHeartbeats 4000000 in
/-- A concrete sequence of model steps reaches the writer's serial image. -/
theorem writer_byte_reachable (elapsed : PID → Nat → Nat) :
    ∃ events last, Run (.start ready (program
        __PATCH__
        __OBSERVE__) elapsed)
      events last ∧ Terminal last (.ok (.integer 9)) ∧ serialState 9 last = true := by
  obtain ⟨events, last, run, done⟩ := terminal_witness (lastFirst := true)
    (expected := 9) (first := .start ready (program
      __PATCH__
      __OBSERVE__) elapsed) (by cbv)
  have correct := patches_agree_with_serial_image elapsed events last _ run done
  exact ⟨events, last, run, done, by simpa only [acceptedObservation, done.outcome_eq] using correct⟩

end Positional.Concurrent
