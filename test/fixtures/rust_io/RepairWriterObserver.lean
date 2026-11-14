module
public import Record.RepairWriterProperties
public import Lynx.Rustler
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace Record.RepairWriterObserver

@[expose] def ackTag : String := "proof:observed-append-acks"
/-- A test observer records only actual successful Rust results. Cell zero is
outside the file/mutex identities and does not allocate or change the counter. -/
@[expose] def recordAck (value : U16) (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.map fun cell =>
    if cell.1 == 0 then (0, ackTag, .cons (.integer value.val) cell.2.2) else cell}

/-- Observation preserves every nonzero cell and every allocation counter. -/
theorem recordAck_frame (value : U16) (env : Environment) (id : Nat) (nonzero : id ≠ 0) :
    (recordAck value env).nativeRefCounter = env.nativeRefCounter ∧
      (recordAck value env).nativeHeap.filter (fun cell => cell.1 == id) =
        env.nativeHeap.filter (fun cell => cell.1 == id) := by
  refine ⟨rfl, ?_⟩
  change (env.nativeHeap.map _).filter _ = _
  generalize env.nativeHeap = cells
  induction cells with
  | nil => rfl
  | cons cell cells ih =>
      by_cases zero : cell.1 = 0
      · simp_all [Ne.symm nonzero]
      · by_cases selected : cell.1 == id <;> simp_all [List.filter_cons]

@[expose] def recorded (value : Nat) : Term → Bool
  | .cons (.integer found) tail => found == value || recorded value tail
  | _ => false
@[expose] def acknowledged (value : Nat) (env : Environment) : Bool :=
  match env.nativeHeap.filter (fun cell => cell.1 == 0) with
  | [(_, tag, entries)] => tag == ackTag && recorded value entries
  | _ => false

@[expose] def observe (value : U16) (operation : NativeM (core.result.Result Bool NativeIoError)) : Result Term := do
  let reply ← operation
  match reply with
  | .Ok true =>
    Result.nativeModify (fun env => ((), recordAck value env)) fun _ => .ok Term.true
  | _ => .ok Term.false

/-- Both successful Rust results must be recorded in the terminal predicate.
A child error leaves its acknowledgement absent, even though process completion
retains the root's result. Observation order need not equal acquisition order. -/
@[expose] def callers (first second : NativeM (core.result.Result Bool NativeIoError)) : Result Term :=
  Result.schedule {} (observe 23#u16 second) fun _ => observe 19#u16 first

end Record.RepairWriterObserver
