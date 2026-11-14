module
public import Shared.FramedCalls
public import Lynx.Modules.Erlang.erlang
public import Shared.Extraction.RustlerAdapter
public section
open Aeneas Aeneas.Std Lynx effects_native
namespace Shared.FramedTermAdapter
set_option maxRecDepth 8192

/-- The generated library adapter retains its actual registration normalization. -/
@[expose] def registeredEnv (env : Environment) : Environment :=
  {env with nativeResourceTypes :=
    (env.nativeResourceTypes ++ [NativeResourceArc.typeName CounterResource]).eraseDups}

private theorem adapter_valid (dispatcher : Dispatcher) (term : Nat) (amount : U64) : Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher (.nativeReference term)
      (Rustler.encodeUnsigned amount) = Rustler.withResourceTypes [NativeResourceArc.typeName CounterResource] (do
        let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
        Rustler.executeNative (__ADD__ owner amount) Rustler.encodeBool) := by
  have decoded : Rustler.decodeUnsigned .U64 64 (Rustler.encodeUnsigned amount) = .ok amount :=
    Rustler.decodeUnsigned_encodeUnsigned amount
  rw [Elixir.LynxEffectsFixture.Native.«counter_add:adapter/2»]
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

/-- Full generated term adaptation uses the real unsigned decoder, retaining the
resource owner on success and disposing it on conversion failure. -/
theorem generated_add_prefix (dispatcher : Dispatcher)
    (pin : NativeResourceArc CounterResource) (term : Nat) (mutex : NativeMutex effects_core.Counter)
    (value amount : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (different : pin.id ≠ mutex.id) :
    ∃ changed updated,
      Result.ReadyPrefix (Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher (.nativeReference term)
        (Rustler.encodeUnsigned amount)) env (.ok (Rustler.encodeBool changed)) {registeredEnv env with
          nativeRefCounter := env.nativeRefCounter + 2,
          nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
            (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
              .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value := updated} : effects_core.Counter)])
            else cell} ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  have registered : NativeResourceArc.typeName CounterResource ∈ (registeredEnv env).nativeResourceTypes := by
    simp [registeredEnv]
  obtain ⟨changed,updated,trace,arithmetic⟩ := Shared.FramedCalls.add_call_prefix pin term mutex
    value amount count poisoned (registeredEnv env) registered positive bounded keys registry token allocation owners stored different
  refine ⟨changed,updated,?_,arithmetic⟩
  rw [adapter_valid dispatcher term amount]
  exact (registration_prefix _ env).trans trace

theorem generated_add_call_next {α : Type} (dispatcher : Dispatcher)
    (pin : NativeResourceArc CounterResource) (term : Nat) (mutex : NativeMutex effects_core.Counter)
    (value amount : U64) (count : Nat) (poisoned : Bool) (env : Environment)
    (next : Term → NativeM α)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode ({state := mutex} : CounterResource)])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == mutex.id) =
      [(mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
        .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value} : effects_core.Counter)])])
    (different : pin.id ≠ mutex.id) :
    ∃ changed updated,
      (Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher (.nativeReference term)
        (Rustler.encodeUnsigned amount) >>= next) env = next (Rustler.encodeBool changed) {registeredEnv env with
          nativeRefCounter := env.nativeRefCounter + 2,
          nativeHeap := env.nativeHeap.map fun cell => if cell.1 == mutex.id then
            (mutex.id,NativeMutex.typeName effects_core.Counter,.tuple #[.atom "unlocked",
              .atom (if poisoned then "poisoned" else "unpoisoned"),NativeCodec.encode ({value := updated} : effects_core.Counter)])
            else cell} ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed,updated,trace,arithmetic⟩ := generated_add_prefix dispatcher pin term mutex value amount count
    poisoned env positive bounded keys registry token allocation owners stored different
  refine ⟨changed,updated,?_,arithmetic⟩
  simpa only [Result.ok_bind] using (trace.bind next).apply

private theorem adapter_rejected (dispatcher : Dispatcher) (term : Nat) (input : Term)
    (rejected : Rustler.decodeUnsigned .U64 64 input = .error (.error (.atom "badarg"))) :
    Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher (.nativeReference term) input =
      Rustler.withResourceTypes [NativeResourceArc.typeName CounterResource] (do
        let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference term)
        resource_release owner
        Result.error (.error (.atom "badarg"))) := by
  rw [Elixir.LynxEffectsFixture.Native.«counter_add:adapter/2»]
  conv_rhs =>
    arg 1
    simp only [NativeResourceArc.typeName,
      Shared.Extraction.NativeCodecs.«typeName::effects_native::CounterResource»]
    cbv
  apply congrArg (Rustler.withResourceTypes _)
  apply congrArg (fun continuation =>
    NativeResourceArc.decode (α := CounterResource) (.nativeReference term) >>= continuation)
  funext owner
  rw [rejected]
  simp only [Result.ofExcept,Result.handle,bind_assoc,Result.error_bind,
    resource_release,monadLift_self]

/-- Failed scalar conversion uses the generated owner cleanup and the original
badarg exception. Existing owners, payloads and unrelated cells are preserved. -/
theorem generated_decoder_failure_prefix (dispatcher : Dispatcher)
    (pin : NativeResourceArc CounterResource) (term : Nat) (payload : CounterResource)
    (count : Nat) (env : Environment) (input : Term)
    (rejected : Rustler.decodeUnsigned .U64 64 input = .error (.error (.atom "badarg")))
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode payload])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count) :
    Result.ReadyPrefix (Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher
      (.nativeReference term) input) env (.error (.error (.atom "badarg")))
      {registeredEnv env with nativeRefCounter := env.nativeRefCounter + 1} := by
  have registered : NativeResourceArc.typeName CounterResource ∈ (registeredEnv env).nativeResourceTypes := by
    simp [registeredEnv]
  have trace := Shared.FramedCalls.decoder_cleanup_prefix (α := Term) pin term payload count (registeredEnv env)
    (.error (.atom "badarg")) registered positive bounded keys registry token allocation owners
  rw [adapter_rejected dispatcher term input rejected]
  exact (registration_prefix _ env).trans trace

theorem generated_decoder_failure_next {β : Type} (dispatcher : Dispatcher)
    (pin : NativeResourceArc CounterResource) (term : Nat) (payload : CounterResource)
    (count : Nat) (env : Environment) (input : Term)
    (rejected : Rustler.decodeUnsigned .U64 64 input = .error (.error (.atom "badarg")))
    (handler : Exception → NativeM Term) (next : Term → NativeM β)
    (positive : 0 < count) (bounded : count < NativeResourceArc.referenceLimit)
    (keys : ∀ cell ∈ env.nativeHeap, cell.1 ≤ env.nativeRefCounter)
    (registry : env.nativeHeap.filter (fun cell => cell.1 == term) =
      [(term,NativeResourceArc.termType CounterResource,.tuple #[.nativeReference pin.id,.nativeReference pin.token])])
    (token : env.nativeHeap.filter (fun cell => cell.1 == pin.token) =
      [(pin.token,NativeResourceArc.handleType CounterResource,.nativeReference pin.id)])
    (allocation : env.nativeHeap.filter (fun cell => cell.1 == pin.id) =
      [(pin.id,NativeResourceArc.typeName CounterResource,
        .tuple #[.integer count,NativeCodec.encode payload])])
    (owners : (env.nativeHeap.filter fun cell =>
      cell.2.1 == NativeResourceArc.handleType CounterResource && cell.2.2 == .nativeReference pin.id).length = count) :
    ((Result.handle (Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher
      (.nativeReference term) input) handler) >>= next) env =
      ((Result.handle (Result.error (.error (.atom "badarg"))) handler) >>= next)
        {registeredEnv env with nativeRefCounter := env.nativeRefCounter + 1} := by
  have trace := generated_decoder_failure_prefix dispatcher pin term payload count env input rejected
    positive bounded keys registry token allocation owners
  exact ((trace.handle handler).bind next).apply

/-- A decoder owner and an actual Rust clone coexist with the VM pin.
The independent resource and unrelated cell are inherited from the base frame. -/
@[expose] def owned (value : U64) (counter : Nat) : Environment :=
  {Shared.Properties.Framed.initialFor value with
    nativeRefCounter := counter
    nativeHeap :=
      (44,NativeResourceArc.handleType CounterResource,.nativeReference 2) ::
      (43,NativeResourceArc.handleType CounterResource,.nativeReference 2) ::
      (Shared.Properties.Framed.heap value 11#u64).map fun cell => if cell.1 == 2 then
        (2,NativeResourceArc.typeName CounterResource,
          .tuple #[.integer 3,NativeCodec.encode ({state := ⟨1⟩} : CounterResource)]) else cell}

@[expose] def initial : Environment := owned 7#u64 44

/-- The prefix contract specializes to arbitrary values, amounts and fresh
counters in a retained-owner frame, without enumerating its execution states. -/
theorem owned_add_prefix (dispatcher : Dispatcher) (value amount : U64) (counter : Nat)
    (counterBound : 44 ≤ counter) :
    ∃ changed updated,
      Result.ReadyPrefix (Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher (.nativeReference 5)
        (Rustler.encodeUnsigned amount)) (owned value counter) (.ok (Rustler.encodeBool changed))
        (owned updated (counter + 2)) ∧
      (if changed then updated.val = value.val + amount.val
       else updated = value ∧ U64.max < value.val + amount.val) := by
  obtain ⟨changed,updated,trace,arithmetic⟩ := generated_add_prefix dispatcher
    (⟨2,4⟩ : NativeResourceArc CounterResource) 5 (⟨1⟩ : NativeMutex effects_core.Counter)
    value amount 3 false (owned value counter) (by decide) (by decide)
    (by simp [owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells]; omega)
    (by simp [owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeMutex.typeName])
    (by simp [owned,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by decide)
  refine ⟨changed,updated,?_,arithmetic⟩
  have dedup : [NativeResourceArc.typeName CounterResource,NativeResourceArc.typeName CounterResource].eraseDups =
      [NativeResourceArc.typeName CounterResource] := by cbv
  simpa [owned,registeredEnv,dedup,Shared.Properties.Framed.initialFor,Shared.Properties.Framed.heap,
    Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells] using trace

/-- Successful addition has a complete native prefix for every admitted amount,
with the exact sum and retained-owner frame supplied to subsequent calls. -/
theorem owned_add_success (dispatcher : Dispatcher) (value amount : U64) (counter : Nat)
    (counterBound : 44 ≤ counter) (fits : value.val + amount.val ≤ U64.max) :
    ∃ updated, Result.ReadyPrefix
      (Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher (.nativeReference 5)
        (Rustler.encodeUnsigned amount)) (owned value counter) (.ok Term.true) (owned updated (counter + 2)) ∧
      updated.val = value.val + amount.val := by
  obtain ⟨changed,updated,trace,arithmetic⟩ := owned_add_prefix dispatcher value amount counter counterBound
  cases changed with
  | false => exact False.elim ((Nat.not_lt_of_ge fits) arithmetic.2)
  | true => exact ⟨updated,trace,arithmetic⟩

/-- Sequence calls to the compiled-export adapter, keeping every returned term.
This is a caller of the extracted implementation, not a replacement for it. -/
@[expose] def addSequence (dispatcher : Dispatcher) : List U64 → Result (List Term)
  | [] => .ok []
  | amount :: rest => do
    let handle ← Erlang.erlang.«get/1» dispatcher (.atom "counter")
    let reply ← Elixir.LynxEffectsFixture.Native.«counter_add/2» dispatcher
      handle (Rustler.encodeUnsigned amount)
    let replies ← addSequence dispatcher rest
    pure (reply :: replies)

/-- Any finite sequence whose total fits preserves the complete retained-owner
frame. Its actual adapter calls all return true and store the exact sum. -/
theorem owned_add_sequence (dispatcher : Dispatcher) (amounts : List U64)
    (value : U64) (counter : Nat) (counterBound : 44 ≤ counter)
    (fits : value.val + (amounts.map UScalar.val).sum ≤ U64.max) :
    ∃ updated, Result.ReadyPrefix (addSequence dispatcher amounts)
      (owned value counter) (.ok (List.replicate amounts.length Term.true))
      (owned updated (counter + 2 * amounts.length)) ∧
      updated.val = value.val + (amounts.map UScalar.val).sum := by
  induction amounts generalizing value counter with
  | nil => exact ⟨value, by simpa [addSequence] using
      (Result.ReadyPrefix.refl (.ok ([] : List Term)) (owned value counter)), by simp⟩
  | cons amount rest ih =>
    have headFits : value.val + amount.val ≤ U64.max := by
      simp only [List.map_cons,List.sum_cons] at fits
      omega
    obtain ⟨middle,headTrace,headSum⟩ := owned_add_success dispatcher value amount counter counterBound headFits
    have tailFits : middle.val + (rest.map UScalar.val).sum ≤ U64.max := by
      simp only [List.map_cons,List.sum_cons] at fits
      omega
    obtain ⟨updated,tailTrace,tailSum⟩ := ih middle (counter + 2) (by omega) tailFits
    refine ⟨updated,?_,?_⟩
    · have first := headTrace.bind (fun reply => do
        let replies ← addSequence dispatcher rest
        pure (reply :: replies))
      have last := tailTrace.bind (fun replies => Result.ok (Term.true :: replies))
      simp only [Result.ok_bind] at first last
      have combined := first.trans last
      have counters : counter + 2 + 2 * rest.length = counter + 2 * (rest.length + 1) := by omega
      simp only [addSequence,Erlang.erlang.«get/1»]
      apply Result.ReadyPrefix.get
      simpa [Result.bind,Result.ok_bind,List.replicate_succ,counters,owned,
        Shared.Properties.Framed.initialFor] using combined
    · simp only [List.map_cons,List.sum_cons]
      omega

/-- The admitted extra owners are produced by the real decoder followed by the
actual extracted internal Rust clone, rather than an assumed ownership header. -/
theorem initial_owners_constructed :
    Result.ReadyPrefix (do
      let owner ← NativeResourceArc.decode (α := CounterResource) (.nativeReference 5)
      resource_clone owner) Shared.Properties.Framed.initial
      (.ok (⟨2,44⟩ : NativeResourceArc CounterResource)) initial := by
  let payload : CounterResource := {state := ⟨1⟩}
  let decoded : Environment := {Shared.Properties.Framed.initial with
    nativeRefCounter := 43
    nativeHeap := (43,NativeResourceArc.handleType CounterResource,.nativeReference 2) ::
      (Shared.Properties.Framed.heap 7#u64 11#u64).map fun cell => if cell.1 == 2 then
        (2,NativeResourceArc.typeName CounterResource,.tuple #[.integer 2,NativeCodec.encode payload]) else cell}
  have pinned : NativeResourceArc.Pinned payload 2 4 5 Shared.Properties.Framed.initial := by
    constructor <;> simp [payload,Shared.Properties.Framed.initial,Shared.Properties.Framed.initialFor,
      Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeMutex.typeName]
  have head := (NativeResourceArc.decode_pinned_prefix payload Shared.Properties.Framed.initial 2 4 5 pinned
    (by simp [Shared.Properties.Framed.initial,Shared.Properties.Framed.initialFor])).bind resource_clone
  simp only [Result.ok_bind] at head
  have tail := Shared.FramedCalls.clone_prefix (⟨2,43⟩ : NativeResourceArc CounterResource)
    payload 2 decoded (by decide) (by decide)
    (by simp [decoded,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [decoded,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
    (by simp [decoded,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells,
      NativeResourceArc.typeName,NativeResourceArc.handleType,NativeResourceArc.termType,NativeMutex.typeName])
    (by simp [decoded,Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells])
  have cloned : Result.ReadyPrefix (resource_clone (⟨2,43⟩ : NativeResourceArc CounterResource))
      decoded (.ok (⟨2,44⟩ : NativeResourceArc CounterResource)) initial := by
    simpa [decoded,initial,owned,payload,Shared.Properties.Framed.initial,Shared.Properties.Framed.initialFor,
      Shared.Properties.Framed.heap,Shared.Properties.Framed.counterCell,NativeResourceArc.vmCells] using tail
  exact head.trans cloned

@[expose] def accepted (value : U64) (counter : Nat) (config : Concurrent.Config Term) : Bool :=
  let env := match config with
    | .start env .. => env
    | .running state .. => state.nativeView []
  let expected := (owned value counter).nativeHeap
  config.outcome.isTrue && env.nativeRefCounter == counter &&
    expected.all env.nativeHeap.contains && env.nativeHeap.length == expected.length &&
    env.nativeResourceTypes.contains (NativeResourceArc.typeName CounterResource)

theorem accepted_outcome (value : U64) (counter : Nat) (config : Concurrent.Config Term)
    (checked : accepted value counter config = true) : config.outcome = .ok Term.true := by
  apply Outcome.eq_of_isTrue
  simp only [accepted,Bool.and_eq_true] at checked
  exact checked.1.1.1.1

end Shared.FramedTermAdapter
