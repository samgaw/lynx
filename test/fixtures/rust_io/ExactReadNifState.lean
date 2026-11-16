module
public import ExactRead.Properties
public section
open Aeneas Aeneas.Std Lynx
namespace ExactRead.Adapter

@[expose] def fileName : ByteArray := NativeFile.bytes (toStr "input")
@[expose] def data (scenario : String) : ByteArray :=
  if scenario == "complete" then ⟨#[7,8]⟩ else
  if scenario == "short" then ⟨#[7]⟩ else ByteArray.empty
@[expose] def action (scenario op : String) (success : Bool) (value : Nat) (rest : Term) : Term :=
  .cons (.tuple #[.atom op,.atom (if success then "ok" else "error"),.integer value,
    .bitstring ⟨(data scenario).data.map (fun _ => 0)⟩ 0]) rest
@[expose] def script (scenario : String) : Term :=
  let closing := action scenario "close" true 0 .nil
  if scenario == "complete" then action scenario "read" true 2 closing else
  if scenario == "short" then action scenario "read" true 1 (action scenario "read" true 0 closing) else
  if scenario == "interrupted" then action scenario "read" false 1 (action scenario "read" true 0 closing) else
  if scenario == "other" then action scenario "read" false 1 closing else
  action scenario "read" true 0 closing
@[expose] def initial (scenario : String) : Environment :=
  let missing := scenario == "missing"
  let names : NativeFile.Names := if missing then [] else [(fileName,3)]
  let opening : Term := .cons (.tuple #[.atom "open",.bitstring fileName 0,
    .atom (if missing then "error" else "ok"),.integer (if missing then 1 else 0),script scenario]) .nil
  { nativeRefCounter := 3,
    nativeHeap := [(0,NativeFile.namespaceTypeName,NativeFile.encodeNamespace ⟨names,names,[],opening⟩)] ++
      (if missing then [] else [(3,NativeFile.inodeTypeName,
        NativeFile.encode ⟨data scenario,data scenario,0,.nil⟩)]) ++
      [(1,NativeIoError.typeName,.atom "live"),
       (2,NativeIoError.kindTypeName,NativeIoError.kindEntry (.os 1)
         (if scenario == "interrupted" then "Interrupted" else "InputOutputError"))] }

@[expose] def complete : Environment := initial "complete"
@[expose] def short : Environment := initial "short"
@[expose] def eof : Environment := initial "eof"
@[expose] def interrupted : Environment := initial "interrupted"
@[expose] def other : Environment := initial "other"
@[expose] def missing : Environment := initial "missing"
end ExactRead.Adapter
