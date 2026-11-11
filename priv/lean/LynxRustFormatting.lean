module
public import Aeneas.Std.Core.Fmt
public import Aeneas.Std.Scalar.Core
public section
open Aeneas Aeneas.Std

namespace Lynx.RustFormatting

/-- Default formatting only. The byte budget is a verification cutoff;
allocation and correspondence to Rust core/alloc remain external boundaries. -/
@[expose, reducible] def core.fmt.Formatter := String

structure core.fmt.Display (Self : Type _) where
  fmt : Self → core.fmt.Formatter → RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

structure core.fmt.Debug (Self : Type _) where
  fmt : Self → core.fmt.Formatter → RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

/-- Formatting arguments retain the actual argument renderer rather than erasing it. -/
@[expose, reducible]
def core.fmt.Arguments : Type :=
  core.fmt.Formatter → RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)

@[expose, reducible]
def core.fmt.rt.Argument : Type := core.fmt.Arguments

namespace Formatting

/-- The bound keeps this default-format model independent of allocator growth.
Larger outputs are verification cutoffs, not simulated Rust panics. -/
@[expose] def append (fmt : core.fmt.Formatter) (text : String) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  let combined := fmt ++ text
  if combined.toUTF8.size ≤ 4294967295 then .ok (.Ok (), combined) else .fail .undef

@[expose] def bytes (values : List U8) : ByteArray :=
  ⟨(values.map (fun value => UInt8.ofNat value.val)).toArray⟩

@[expose] def writeBytes (fmt : core.fmt.Formatter) (values : List UInt8) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  match String.fromUTF8? ⟨values.toArray⟩ with
  | some text => append fmt text
  | none => .fail .undef

/-- Rust 1.100's format-argument bytecode, restricted to default sequential
placeholders and UTF-8 literals (short or 16-bit length). Options, bad indices,
invalid UTF-8, malformed templates and trailing bytes are verification cutoffs.
Each step consumes a byte, so `template.length + 1` supplies sufficient fuel. -/
@[expose] def run : Nat → List UInt8 → List core.fmt.rt.Argument → Nat →
    core.fmt.Formatter → RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter)
  | 0, _, _, _, _ => .fail .undef
  | _ + 1, [], _, _, _ => .fail .undef
  | fuel + 1, tag :: rest, args, index, fmt => do
    let literal (size : Nat) (tail : List UInt8) := do
      if size ≤ tail.length then
        let (result, next) ← writeBytes fmt (tail.take size)
        match result with
        | .Err error => .ok (.Err error, next)
        | .Ok () => run fuel (tail.drop size) args index next
      else .fail .undef
    if tag.toNat = 0 then
      if rest.isEmpty then .ok (.Ok (), fmt) else .fail .undef
    else if tag.toNat < 128 then literal tag.toNat rest
    else if tag.toNat = 128 then
      match rest with
      | lo :: hi :: tail => literal (lo.toNat + 256 * hi.toNat) tail
      | _ => .fail .undef
    else if tag.toNat = 192 then
      match args[index]? with
      | none => .fail .undef
      | some render =>
        let (result, next) ← render fmt
        match result with
        | .Err error => .ok (.Err error, next)
        | .Ok () => run fuel rest args (index + 1) next
    else .fail .undef

@[simp] theorem append_eq (fmt : core.fmt.Formatter) (text : String)
    (bound : (fmt ++ text).toUTF8.size ≤ 4294967295) :
    append fmt text = RustM.ok (.Ok (), fmt ++ text) := by simp only [append, ite_eq_left bound]

@[simp] theorem writeBytes_eq (fmt : core.fmt.Formatter) (values : List UInt8) (text : String)
    (valid : String.fromUTF8? ⟨values.toArray⟩ = some text)
    (bound : (fmt ++ text).toUTF8.size ≤ 4294967295) :
    writeBytes fmt values = RustM.ok (.Ok (), fmt ++ text) := by
  simp only [writeBytes, valid]
  exact append_eq fmt text bound

/-- Check the supported subset before admitting the unsafe Rust constructor. -/
@[expose] def validTemplate : Nat → List UInt8 → Nat → Nat → Bool
  | 0, _, _, _ => false
  | _ + 1, [], _, _ => false
  | fuel + 1, tag :: rest, count, index =>
    let literal (size : Nat) (tail : List UInt8) :=
      size ≤ tail.length &&
        (String.fromUTF8? ⟨(tail.take size).toArray⟩).isSome &&
        validTemplate fuel (tail.drop size) count index
    if tag.toNat = 0 then rest.isEmpty
    else if tag.toNat < 128 then literal tag.toNat rest
    else if tag.toNat = 128 then
      match rest with
      | lo :: hi :: tail => literal (lo.toNat + 256 * hi.toNat) tail
      | _ => false
    else if tag.toNat = 192 then index < count && validTemplate fuel rest count (index + 1)
    else false


end Formatting

@[expose]
def core.fmt.Arguments.from_str (text : Str) : RustM core.fmt.Arguments :=
  .ok (fun fmt => Formatting.writeBytes fmt (Formatting.bytes text.val).toList)

@[expose]
def core.fmt.Arguments.new {N : Std.Usize} {M : Std.Usize}
  (template : Std.Array Std.U8 N) (args : Std.Array core.fmt.rt.Argument M) : RustM core.fmt.Arguments :=
  let program := (Formatting.bytes template.val).toList
  if Formatting.validTemplate (program.length + 1) program args.val.length 0 then
    .ok (Formatting.run (program.length + 1) program args.val 0)
  else .fail .undef

@[expose]
def core.fmt.Formatter.write_str (fmt : core.fmt.Formatter) (text : Str) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  Formatting.writeBytes fmt (Formatting.bytes text.val).toList

@[expose]
def core.fmt.Formatter.write_fmt
  (fmt : core.fmt.Formatter) (args : core.fmt.Arguments) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) := args fmt

@[expose]
def core.fmt.DisplayShared.fmt {T : Type _} (inst : core.fmt.Display T) (value : T)
    (fmt : core.fmt.Formatter) : RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  inst.fmt value fmt

@[expose]
def core.fmt.DisplayStr.fmt (value : Str) (fmt : core.fmt.Formatter) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  core.fmt.Formatter.write_str fmt value

@[expose]
def alloc.string.DisplayString.fmt (value : String) (fmt : core.fmt.Formatter) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  Formatting.append fmt value

/-- Default formatting of the actual Display implementation. A Display error
panics in Rust's ToString blanket implementation. -/
@[expose]
def alloc.string.ToString.to_string {T : Type _} (inst : core.fmt.Display T) (value : T) :
    RustM String := do
  let (result, text) ← inst.fmt value ""
  match result with
  | .Ok () => .ok text
  | .Err _ => .fail .panic

/-- Allocated default formatting. Native capacity and allocation success remain
external boundaries. A formatter error triggers Rust's expect panic, while an
oversized result is a verification cutoff. -/
@[expose]
def alloc.fmt.format (args : core.fmt.Arguments) : RustM String := do
  let (result, text) ← args ""
  match result with
  | .Ok () => if text.utf8ByteSize ≤ 4294967295 ∧ text.utf8ByteSize ≤ Isize.max.toNat then .ok text else .fail .undef
  | .Err _ => .fail .panic

theorem alloc.fmt.format_success (args : core.fmt.Arguments) (text : String)
    (rendered : args "" = .ok (.Ok (), text)) (bound : text.utf8ByteSize ≤ 4294967295 ∧ text.utf8ByteSize ≤ Isize.max.toNat) :
    alloc.fmt.format args = .ok text := by simp [alloc.fmt.format, rendered, bound]

theorem alloc.fmt.format_error (args : core.fmt.Arguments) (text : String) (error : core.fmt.Error)
    (rendered : args "" = .ok (.Err error, text)) :
    alloc.fmt.format args = .fail .panic := by simp [alloc.fmt.format, rendered]

theorem alloc.fmt.format_exhausted (args : core.fmt.Arguments) (text : String)
    (rendered : args "" = .ok (.Ok (), text)) (outside : ¬ (text.utf8ByteSize ≤ 4294967295 ∧ text.utf8ByteSize ≤ Isize.max.toNat)) :
    alloc.fmt.format args = .fail .undef := by simp [alloc.fmt.format, rendered, outside]

@[expose]
def core.fmt.rt.Argument.new_display
  {T : Type _} (inst : core.fmt.Display T) (value : T) : RustM core.fmt.rt.Argument :=
  .ok (inst.fmt value)

@[expose] def core.fmt.rt.Argument.new_debug
    {T : Type _} (inst : core.fmt.Debug T) (value : T) : RustM core.fmt.rt.Argument :=
  .ok (inst.fmt value)

/-- An unused foreign formatter dictionary is not callable semantics. -/
@[expose] def Formatting.unavailable {T : Type} (_ : T) (_ : core.fmt.Formatter) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) := .fail .undef

/-- ASCII subset of OTP native `%T` printing. Names containing `@` need
quotes in this printer. Supported names fit the first 1024-byte buffer;
quoting, escapes and non-ASCII printing remain cutoffs. -/
@[expose] def Formatting.bareAtom (value : String) : Bool :=
  match value.toList with
  | [] => false
  | first :: rest => value.toUTF8.size ≤ 255 && first ≥ 'a' && first ≤ 'z' &&
      rest.all (fun c => (c ≥ 'a' && c ≤ 'z') || (c ≥ 'A' && c ≤ 'Z') ||
        (c ≥ '0' && c ≤ '9') || c == '_')

theorem Formatting.bareAtom_at_cutoff : Formatting.bareAtom "a@b" = false := by
  simp [Formatting.bareAtom]

@[expose] def rustler.atom.Debug.fmt (value : String) (fmt : core.fmt.Formatter) :
    RustM (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  if Formatting.bareAtom value then Formatting.append fmt value else .fail .undef

@[expose, simp]
def core.fmt.num.imp.DisplayU8.fmt : Std.U8 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayU16.fmt : Std.U16 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayU32.fmt : Std.U32 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayU64.fmt : Std.U64 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayU128.fmt : Std.U128 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayUsize.fmt : Std.Usize → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayI8.fmt : Std.I8 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayI16.fmt : Std.I16 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayI32.fmt : Std.I32 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayI64.fmt : Std.I64 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayI128.fmt : Std.I128 → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)

@[expose, simp]
def core.fmt.num.imp.DisplayIsize.fmt : Std.Isize → core.fmt.Formatter →
  RustM ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  fun value fmt => Formatting.append fmt (toString value.val)


end Lynx.RustFormatting
