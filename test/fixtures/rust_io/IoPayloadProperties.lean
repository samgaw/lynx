module
public import IoPayload.Extraction.Funs
public section
open Aeneas Aeneas.Std Lynx io_protocol
namespace IoPayload.Properties

@[expose] def retryable : core.io.error.ErrorKind → Bool
  | .Interrupted => true
  | _ => false

theorem core_spec (kind : core.io.error.ErrorKind) :
    io_core.is_retryable kind = Result.ok (retryable kind) := by
  cases kind <;>
    simp [io_core.is_retryable, core.io.error.ErrorKind.Insts.CoreCmpPartialEqErrorKind.eq,
      retryable, core.io.error.ErrorKind.read_discriminant,
      NativeM.lift, NativeM.ok]

/-- The actual borrowed getter preserves every field of the native environment. -/
theorem borrowed_kind (error : NativeIoError) (env : Environment) (label : String)
    (kind : core.io.error.ErrorKind)
    (admitted : NativeIoError.getKind error env = .ok label)
    (decoded : IoPayload.Extraction.IoErrorModel.decodeKind label = .ok kind) :
    Result.ReadyPrefix (io_core.error_kind error) env (.ok kind) env := by
  simp only [io_core.error_kind, IoPayload.Extraction.IoErrorModel.kind,
    NativeIoError.kind, monadLift_self, Result.nativeGet_bind]
  apply Result.ReadyPrefix.nativeGet
  simpa only [admitted, decoded, Result.ofExcept_ok, Result.ok_bind] using
    Result.ReadyPrefix.refl (.ok kind) env

/-- Composition uses the actual cross-crate getter and extracted standard comparison. -/
theorem classified (error : NativeIoError) (env : Environment) (label : String)
    (kind : core.io.error.ErrorKind)
    (admitted : NativeIoError.getKind error env = .ok label)
    (decoded : IoPayload.Extraction.IoErrorModel.decodeKind label = .ok kind) :
    Result.ReadyPrefix (error_is_retryable error) env (.ok (retryable kind)) env := by
  simp only [error_is_retryable, monadLift_self, core_spec]
  have first := (borrowed_kind error env label kind admitted decoded).bind
    (fun value => Result.ok (retryable value))
  simpa only [Result.ok_bind] using first

@[expose] def one : Slice U8 := .from [0#u8] (by scalar_tac)
@[expose] def disposed (error : NativeIoError) (env : Environment) : Environment :=
  {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != error.identity)}

@[expose] def classifyDrop (error : NativeIoError) : NativeM Bool := do
  let answer ← error_is_retryable error
  NativeIoError.dispose error
  NativeM.ok answer

@[expose] def finishRead (file : NativeFile)
    (reply : core.result.Result Usize NativeIoError) : NativeM Bool := do
  let answer ← match reply with
    | .Ok _ => NativeM.ok false
    | .Err error => classifyDrop error
  NativeFile.close file
  NativeM.ok answer

/-- Normalization retains actual reads, current file state and both owning drops. -/
theorem read_contract (path : Str) : read_is_retryable path = (do
    let opened ← io_core.open_readonly path
    match opened with
    | .Err error => classifyDrop error
    | .Ok file =>
      let (reply,returned,_) ← io_core.read_once file one
      finishRead returned reply) := by
  simp only [read_is_retryable, monadLift_self, NativeM.lift, NativeM.ok,
    Result.ok_bind, Array.to_slice_mut, Array.to_slice, Array.make_val, NativeOwnedDrop.drop]
  apply congrArg (fun next => io_core.open_readonly path >>= next)
  funext reply
  cases reply with
  | Err error => rfl
  | Ok file =>
    change (io_core.read_once file one >>= _) = _
    apply congrArg (fun next => io_core.read_once file one >>= next)
    funext result
    obtain ⟨reply,returned,buffer⟩ := result
    cases reply <;> simp [finishRead,classifyDrop,NativeM.ok,bind_assoc]

theorem classify_drop (error : NativeIoError) (env : Environment) (label : String)
    (kind : core.io.error.ErrorKind)
    (admitted : NativeIoError.getKind error env = .ok label)
    (decoded : IoPayload.Extraction.IoErrorModel.decodeKind label = .ok kind)
    (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ env.nativeRefCounter)
    (stored : env.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "live")]) :
    Result.ReadyPrefix (classifyDrop error) env (.ok (retryable kind)) (disposed error env) := by
  unfold classifyDrop
  apply ((classified error env label kind admitted decoded).bind _).trans
  simp only [Result.ok_bind]
  have removed := (NativeIoError.dispose_prefix error env nonzero bounded stored).bind
    (fun _ => NativeM.ok (retryable kind))
  simpa only [NativeM.ok,Result.ok_bind,disposed] using removed

theorem open_error (path : Str) (before opened : Environment) (error : NativeIoError)
    (label : String) (kind : core.io.error.ErrorKind)
    (poll : NativeFile.pollOpenReadOnly path before = some (.ok (.Err error),opened))
    (admitted : NativeIoError.getKind error opened = .ok label)
    (decoded : IoPayload.Extraction.IoErrorModel.decodeKind label = .ok kind)
    (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ opened.nativeRefCounter)
    (stored : opened.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "live")]) :
    Result.ReadyPrefix (read_is_retryable path) before (.ok (retryable kind)) (disposed error opened) := by
  simp only [read_contract,io_core.open_readonly,monadLift_self,NativeFile.openReadOnly,
    Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ poll
  simpa only [Result.ok_bind] using classify_drop error opened label kind admitted decoded nonzero bounded stored

theorem read_error (path : Str) (before opened readEnv after : Environment)
    (file returned : NativeFile) (buffer : Slice U8) (error : NativeIoError)
    (label : String) (kind : core.io.error.ErrorKind)
    (opening : NativeFile.pollOpenReadOnly path before = some (.ok (.Ok file),opened))
    (read : NativeFile.pollRead file one opened = some (.ok (.Err error,returned,buffer),readEnv))
    (admitted : NativeIoError.getKind error readEnv = .ok label)
    (decoded : IoPayload.Extraction.IoErrorModel.decodeKind label = .ok kind)
    (nonzero : error.identity ≠ 0) (bounded : error.identity ≤ readEnv.nativeRefCounter)
    (stored : readEnv.nativeHeap.filter (fun cell => cell.1 == error.identity) =
      [(error.identity,NativeIoError.typeName,.atom "live")])
    (closing : NativeFile.pollClose returned (disposed error readEnv) = some (.ok (),after)) :
    Result.ReadyPrefix (read_is_retryable path) before (.ok (retryable kind)) after := by
  simp only [read_contract,io_core.open_readonly,monadLift_self,NativeFile.openReadOnly,
    Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ opening
  simp only [Result.ok_bind,io_core.read_once,NativeFile.read,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ read
  simp only [Result.ok_bind,finishRead]
  apply ((classify_drop error readEnv label kind admitted decoded nonzero bounded stored).bind _).trans
  simp only [Result.ok_bind,NativeFile.close,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ closing
  simpa only [Result.ok_bind,NativeM.ok] using Result.ReadyPrefix.refl (.ok (retryable kind)) after

theorem read_success (path : Str) (before opened readEnv after : Environment)
    (file returned : NativeFile) (buffer : Slice U8) (count : Usize)
    (opening : NativeFile.pollOpenReadOnly path before = some (.ok (.Ok file),opened))
    (read : NativeFile.pollRead file one opened = some (.ok (.Ok count,returned,buffer),readEnv))
    (closing : NativeFile.pollClose returned readEnv = some (.ok (),after)) :
    Result.ReadyPrefix (read_is_retryable path) before (.ok false) after := by
  simp only [read_contract,io_core.open_readonly,monadLift_self,NativeFile.openReadOnly,
    Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ opening
  simp only [Result.ok_bind,io_core.read_once,NativeFile.read,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ read
  simp only [Result.ok_bind,finishRead,NativeM.ok,NativeFile.close,Result.wait_bind]
  apply Result.ReadyPrefix.wait _ _ _ _ _ _ _ closing
  simpa only [Result.ok_bind,NativeM.ok] using Result.ReadyPrefix.refl (.ok false) after

@[expose] def error : NativeIoError := ⟨1⟩
@[expose] def metadata (label : String) : Nat × String × Term :=
  (2, NativeIoError.kindTypeName, NativeIoError.kindEntry error label)
@[expose] def path : Str := toStr "missing"
@[expose] def fileName : ByteArray := NativeFile.bytes path

inductive Scenario where
  | openNotFound | interruptedRead | otherRead | completeRead | eofRead
  deriving DecidableEq

@[expose] def label : Scenario → String
  | .interruptedRead => "Interrupted"
  | .otherRead => "InputOutputError"
  | _ => "NotFound"
@[expose] def classifiedKind : Scenario → core.io.error.ErrorKind
  | .interruptedRead => .Interrupted
  | .otherRead => .InputOutputError
  | _ => .NotFound
@[expose] def expected : Scenario → Bool
  | .interruptedRead => true
  | _ => false
@[expose] def hasError : Scenario → Bool
  | .openNotFound | .interruptedRead | .otherRead => true
  | _ => false
@[expose] def data : Scenario → ByteArray
  | .eofRead => ⟨#[]⟩
  | _ => ⟨#[7]⟩
@[expose] def disk (scenario : Scenario) : NativeFile.State :=
  ⟨data scenario, data scenario, 0, .nil⟩
@[expose] def mask (scenario : Scenario) : ByteArray := ⟨(data scenario).data.map (fun _ => 0)⟩
@[expose] def action (scenario : Scenario) (op : String) (success : Bool) (value : Nat)
    (rest : Term) : Term := .cons (.tuple #[.atom op,.atom (if success then "ok" else "error"),
      .integer value,.bitstring (mask scenario) 0]) rest
@[expose] def closing (scenario : Scenario) : Term := action scenario "close" true 0 .nil
@[expose] def ioScript (scenario : Scenario) : Term :=
  match scenario with
  | .interruptedRead | .otherRead => action scenario "read" false 1 (closing scenario)
  | .eofRead => action scenario "read" true 0 (closing scenario)
  | _ => action scenario "read" true 1 (closing scenario)
@[expose] def names : Scenario → NativeFile.Names
  | .openNotFound => []
  | _ => [(fileName,3)]
@[expose] def opening (scenario : Scenario) : Term := .cons
  (.tuple #[.atom "open",.bitstring fileName 0,
    .atom (match scenario with | .openNotFound => "error" | _ => "ok"),
    .integer (match scenario with | .openNotFound => 1 | _ => 0),ioScript scenario]) .nil
@[expose] def namespaceCell (scenario : Scenario) (script : Term) : Nat × String × Term :=
  (0, NativeFile.namespaceTypeName, NativeFile.encodeNamespace ⟨names scenario,names scenario,[],script⟩)
@[expose] def inodeCell (scenario : Scenario) : List (Nat × String × Term) :=
  match scenario with
  | .openNotFound => []
  | _ => [(3,NativeFile.inodeTypeName,NativeFile.encode (disk scenario))]
@[expose] def errorCell (scenario : Scenario) : List (Nat × String × Term) :=
  if hasError scenario then [(1,NativeIoError.typeName,.atom "live")] else []
@[expose] def initial (scenario : Scenario) : Environment := {
  nativeRefCounter := 3
  nativeHeap := [namespaceCell scenario (opening scenario)] ++ inodeCell scenario ++
    errorCell scenario ++ [metadata (label scenario)] }
@[expose] def opened (scenario : Scenario) : Environment := {
  nativeRefCounter := if scenario = .openNotFound then 3 else 4
  nativeHeap := (if scenario = .openNotFound then [] else
    [(4,NativeFile.handleTypeName,NativeFile.encodeHandle ⟨3,0,ioScript scenario⟩)]) ++
    [namespaceCell scenario .nil] ++ inodeCell scenario ++ errorCell scenario ++
    [metadata (label scenario)] }
@[expose] def position : Scenario → Nat
  | .completeRead => 1
  | _ => 0
@[expose] def readEnv (scenario : Scenario) : Environment := {
  nativeRefCounter := 4
  nativeHeap := [(4,NativeFile.handleTypeName,NativeFile.encodeHandle ⟨3,position scenario,closing scenario⟩),
    namespaceCell scenario .nil] ++ inodeCell scenario ++ errorCell scenario ++ [metadata (label scenario)] }
@[expose] def finished (scenario : Scenario) : Environment := {
  nativeRefCounter := if scenario = .openNotFound then 3 else 4
  nativeHeap := (if scenario = .openNotFound then [] else
    [(4,NativeFile.closedHandleTypeName,NativeFile.encodeHandle ⟨3,position scenario,.nil⟩)]) ++
    [namespaceCell scenario .nil] ++ inodeCell scenario ++ [metadata (label scenario)] }

/-- Actual open/read/close polls witness errors, interruption, complete reads and EOF. -/
theorem scenarios (scenario : Scenario) :
    Result.ReadyPrefix (read_is_retryable path) (initial scenario) (.ok (expected scenario))
      (finished scenario) := by
  cases scenario with
  | openNotFound =>
    exact open_error path (initial .openNotFound) (opened .openNotFound) error "NotFound" .NotFound
      (by cbv) (by cbv) (by rfl) (by decide) (by decide) (by cbv)
  | interruptedRead =>
    exact read_error path (initial .interruptedRead) (opened .interruptedRead) (readEnv .interruptedRead) (finished .interruptedRead) ⟨4⟩ ⟨4⟩ one error "Interrupted" .Interrupted
      (by cbv) (by cbv) (by cbv) (by rfl) (by decide) (by decide) (by cbv) (by cbv)
  | otherRead =>
    exact read_error path (initial .otherRead) (opened .otherRead) (readEnv .otherRead) (finished .otherRead) ⟨4⟩ ⟨4⟩ one error "InputOutputError" .InputOutputError
      (by cbv) (by cbv) (by cbv) (by rfl) (by decide) (by decide) (by cbv) (by cbv)
  | completeRead =>
    exact read_success path (initial .completeRead) (opened .completeRead) (readEnv .completeRead) (finished .completeRead) ⟨4⟩ ⟨4⟩ (.from [7#u8] (by scalar_tac)) 1#usize
      (by cbv) (by cbv) (by cbv)
  | eofRead =>
    exact read_success path (initial .eofRead) (opened .eofRead) (readEnv .eofRead) (finished .eofRead) ⟨4⟩ ⟨4⟩ one 0#usize
      (by cbv) (by cbv) (by cbv)

/-- Every terminal native run retains the result and exact post-read cleanup state. -/
theorem every_run (scenario : Scenario) (elapsed : PID → Nat → Nat)
    (run : Concurrent.Run (.start (initial scenario) (read_is_retryable path) elapsed) events last)
    (terminal : Concurrent.Terminal last outcome) :
    last = .start (finished scenario) (.ok (expected scenario)) elapsed ∧ outcome = .ok (expected scenario) := by
  obtain ⟨_,rest⟩ := (scenarios scenario).terminalRun elapsed run terminal
  cases rest with
  | refl => exact ⟨rfl,terminal.outcome_eq.symm⟩
  | step step _ => simp [Concurrent.Step,Concurrent.Config.successors,Concurrent.isRequest] at step

@[expose] def interrupted : Environment := initial .interruptedRead
@[expose] def missing : Environment := initial .openNotFound
@[expose] def other : Environment := initial .otherRead
@[expose] def complete : Environment := initial .completeRead
@[expose] def eof : Environment := initial .eofRead

inductive Invalid where
  | missingMetadata | duplicateMetadata | wrongMetadataType | wrongMetadataPayload
  | metadataAlias | metadataUnbounded | missingError | customError | zeroError | unknownKind
  | wrongMetadataOwner | zeroMetadata | wrongErrorType
  deriving DecidableEq

@[expose] def invalid (case_ : Invalid) : Environment :=
  let env := initial .interruptedRead
  match case_ with
  | .missingMetadata => {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != 2)}
  | .duplicateMetadata => {env with nativeHeap := metadata "Interrupted" :: env.nativeHeap}
  | .wrongMetadataType => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 2 then (2,"wrong-type",cell.2.2) else cell}
  | .wrongMetadataPayload => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 2 then (2,cell.2.1,.integer 0) else cell}
  | .metadataAlias => {env with nativeHeap := (2,"unrelated",.nil) :: env.nativeHeap}
  | .metadataUnbounded => {env with nativeRefCounter := 1}
  | .missingError => {env with nativeHeap := env.nativeHeap.filter (fun cell => cell.1 != 1)}
  | .customError => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 1 then (1,NativeIoError.typeName,.atom "custom") else cell}
  | .zeroError => env
  | .wrongMetadataOwner => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 2 then (2,cell.2.1,NativeIoError.kindEntry ⟨99⟩ "Interrupted") else cell}
  | .zeroMetadata => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 2 then (0,cell.2.1,cell.2.2) else cell}
  | .wrongErrorType => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 1 then (1,"wrong-error-type",cell.2.2) else cell}
  | .unknownKind => {env with nativeHeap := env.nativeHeap.map fun cell =>
      if cell.1 == 2 then (2,cell.2.1,NativeIoError.kindEntry error "not-a-kind") else cell}

theorem unavailable (error : NativeIoError) (env : Environment)
    (missing : NativeIoError.getKind error env = .error .exhausted) :
    Result.ReadyPrefix (error_is_retryable error) env (.error .exhausted) env := by
  simp only [error_is_retryable,io_core.error_kind,monadLift_self,
    IoPayload.Extraction.IoErrorModel.kind,NativeIoError.kind,Result.nativeGet_bind]
  apply Result.ReadyPrefix.nativeGet
  simp only [missing,Result.ofExcept_error,Result.error_bind]
  exact .refl _ _

theorem unrecognized (error : NativeIoError) (env : Environment) (label : String)
    (admitted : NativeIoError.getKind error env = .ok label)
    (unknown : IoPayload.Extraction.IoErrorModel.decodeKind label = .error .exhausted) :
    Result.ReadyPrefix (error_is_retryable error) env (.error .exhausted) env := by
  simp only [error_is_retryable,io_core.error_kind,monadLift_self,
    IoPayload.Extraction.IoErrorModel.kind,NativeIoError.kind,Result.nativeGet_bind]
  apply Result.ReadyPrefix.nativeGet
  simp only [admitted,unknown,Result.ofExcept_ok,Result.ok_bind,
    Result.ofExcept_error,Result.error_bind]
  exact .refl _ _

/-- Unsupported classification exhausts the actual Rust caller without changing state. -/
theorem rejected (case_ : Invalid) :
    Result.ReadyPrefix (error_is_retryable (if case_ = .zeroError then ⟨0⟩ else error))
      (invalid case_) (.error .exhausted) (invalid case_) := by
  cases case_ with
  | unknownKind =>
    exact unrecognized error (invalid .unknownKind) "not-a-kind" (by
      simp [NativeIoError.getKind,NativeIoError.kindTypeName,NativeIoError.kindEntry,NativeIoError.decodeKindEntry,invalid,initial,namespaceCell,
        inodeCell,errorCell,metadata,error,hasError,label,NativeIoError.typeName,
        NativeFile.namespaceTypeName,NativeFile.inodeTypeName])
      (by simp [IoPayload.Extraction.IoErrorModel.decodeKind])
  | _ =>
    apply unavailable
    simp [NativeIoError.getKind,NativeIoError.kindTypeName,NativeIoError.kindEntry,NativeIoError.decodeKindEntry,invalid,initial,namespaceCell,
      inodeCell,errorCell,metadata,error,hasError,label,NativeIoError.typeName,
      NativeFile.namespaceTypeName,NativeFile.inodeTypeName]

@[expose] def noMetadata : Environment := invalid .missingMetadata
@[expose] def unknownKind : Environment := invalid .unknownKind

end IoPayload.Properties
